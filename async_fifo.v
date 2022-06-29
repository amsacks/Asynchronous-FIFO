/* Description:   An asynchronous FIFO that allows the buffering of data between
                  two clock domains. The empty and full status flags are asserted
                  immediately, but are removed pessimistically (i.e. 2 clock cycles late)
                  due to the latency of using double Flip-Flops to synchronize the write
                  and read pointers between the clock domains.
                  
                  http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
                
*/

module async_fifo
    #(  parameter WIDTH        = 4,
        parameter DEPTH        = 16,        // NOTE: Must be a power of 2
        parameter ALMOST_FULL  = 8,         
        parameter ALMOST_EMPTY = 8 )
    (   input              w_clk,
        input              w_rst,
        input              w_en,
        input [WIDTH-1:0]  i_dat,
        output reg         w_almost_full,
        output reg         w_full,
        
        input              r_clk, 
        input              r_rst,
        input              r_en,
        output [WIDTH-1:0] o_dat,
        output reg         r_almost_empty, 
        output reg         r_empty
    );
    
    localparam bitDEPTH = $clog2(DEPTH); 
    
    // wire/reg for write-domain logic
    wire [bitDEPTH - 1 : 0] waddr;     
    wire [bitDEPTH     : 0] wgraynext;
    wire [bitDEPTH     : 0] wbinnext;
    wire                    wfull_val;
    wire                    walmost_full_val;
    
    reg [bitDEPTH: 0] wbin;
    reg [bitDEPTH: 0] wptr; 
    reg [bitDEPTH: 0] wq1_rptr;
    reg [bitDEPTH: 0] wq2_rptr; 

    // wire/reg for read-domain logic
    wire [bitDEPTH - 1 :0] raddr;   
    wire [bitDEPTH     :0] rgraynext;
    wire [bitDEPTH     :0] rbinnext; 
    wire                   rempty_val;
    wire                   ralmost_empty_val;

    reg [bitDEPTH      :0] rbin; 
    reg [bitDEPTH      :0] rptr;
    reg [bitDEPTH      :0] rq1_wptr;
    reg [bitDEPTH      :0] rq2_wptr;
    
    
    // FIFO Memory Style: Synchronous Dual-Port RAM
    reg [WIDTH - 1:0] mem [DEPTH - 1:0]; 
    
    assign o_dat = mem[raddr]; 

    always @(posedge w_clk)
        if(w_en && !w_full) mem[waddr] <= i_dat; 
   
   /** =======================================================
      
                            Read-Domain Logic
   
       ======================================================= **/ 
       
    // Double FF to synchronize write pointer to read clock domain
    always @(posedge r_clk or posedge r_rst)
        begin
            if(r_rst) {rq2_wptr, rq1_wptr} <= 0;
            else      {rq2_wptr, rq1_wptr} <= {rq1_wptr, wptr}; 
        end 
    
    // Read Binary and Gray pointer STYLE #2 
    always @(posedge r_clk or posedge r_rst)
        begin
            if(r_rst) {rbin, rptr} <= 0;
            else      {rbin, rptr} <= {rbinnext, rgraynext}; 
        end 
    
    // Use binary to address FIFO memory. Use Gray for synchronizing and logic for almost empty/empty flags. 
    assign raddr     =  rbin[bitDEPTH-1:0];  
    assign rbinnext  =  rbin + (r_en & (~r_empty));
    assign rgraynext = (rbinnext >> 1) ^ rbinnext; 
    
    
    // Logic for FIFO is empty
    always @(posedge r_clk or posedge r_rst)
        begin
            if(r_rst) r_empty <= 1'b1;
            else      r_empty <= rempty_val; 
        end 
    
    assign rempty_val = (rq2_wptr == rgraynext); 
   


   // Logic for FIFO is almost empty in 3 steps.
   wire [bitDEPTH :0] rq2_wptr_bin;  
   wire [bitDEPTH :0] rbin_wbin_diff;
   
   // 1st: Convert write pointer in gray code to binary
   assign rq2_wptr_bin[bitDEPTH] = rq2_wptr[bitDEPTH]; 
   generate
        genvar k;
        for(k = bitDEPTH - 1; k >= 0; k = k - 1)        
            begin
                assign rq2_wptr_bin[k] = rq2_wptr_bin[k+1] ^ rq2_wptr[k];
            end
        endgenerate
   
   // 2nd: Find difference between binary read and write pointers.
   /*      Check whether the difference is within the threshold.
            - There are two cases since a FIFO is a circular queue.
                Case 1: read pointer > write pointer. 
                    
                    Logic for difference: diff = rptr_bin - wptr_bin
                     
                Case 2: read pointer <= write pointer                                             
            
                    Logic for difference: diff = (wptr_bin - rptr_bin)
                    
   */
   assign rbin_wbin_diff     = (rbinnext > rq2_wptr_bin) ? (rbinnext - rq2_wptr_bin) 
                                                            : (rq2_wptr_bin - rbinnext);
   assign ralmost_empty_val  = (rbin_wbin_diff >= ALMOST_EMPTY);
    
   // 3rd: Assign to the top module output almost empty. On reset, if FIFO depth is 
   //      greater than ALMOST_EMPTY, then r_almost_empty = 1'b0.
   always @(posedge r_clk or posedge r_rst)
       begin
           if(r_rst) r_almost_empty <= 0;
           else      r_almost_empty <= ralmost_empty_val;
       end
       
       
    /** =======================================================
      
                            Write-Domain Logic
   
       ======================================================= **/   
       
    // Double FF to synchronize read pointer to write clock domain
    always @(posedge w_clk or posedge w_rst)
        begin
            if(w_rst) {wq2_rptr, wq1_rptr} <= 0;
            else      {wq2_rptr, wq1_rptr} <= {wq1_rptr, rptr}; 
        end  
    
    // Write Binary and Gray pointer STYLE #2 
    always @(posedge w_clk or posedge w_rst)
        begin
            if(w_rst) {wbin, wptr} <= 0;
            else      {wbin, wptr} <= {wbinnext, wgraynext}; 
        end
           
    // Use binary to address FIFO memory. Use Gray for synchronizing and logic for almost empty/empty flags   
    assign waddr     = wbin[bitDEPTH-1:0];
    assign wbinnext  = wbin + (w_en & ~w_full);
    assign wgraynext = (wbinnext >> 1) ^ wbinnext; 
    
    
    // Logic for FIFO is full
    always @(posedge w_clk or posedge w_rst)
        begin
            if(w_rst) w_full <= 1'b0;
            else      w_full <= wfull_val; 
        end 
    
    assign wfull_val = ((wgraynext[bitDEPTH]     != wq2_rptr[bitDEPTH])   &&
                        (wgraynext[bitDEPTH-1]   != wq2_rptr[bitDEPTH-1]) &&
                        (wgraynext[bitDEPTH-2:0] == wq2_rptr[bitDEPTH-2:0])); 
    
    // Logic for FIFO is almost full (similar to logic for when FIFO is empty)
    wire [bitDEPTH :0] wq2_rptr_bin;  
    wire [bitDEPTH :0] wbin_rbin_diff;
    assign wq2_rptr_bin[bitDEPTH] = wq2_rptr[bitDEPTH]; 
    generate 
        genvar j;
        for(j = bitDEPTH - 1; j >= 0; j = j - 1)
            begin
                assign wq2_rptr_bin[j] = wq2_rptr_bin[j+1] ^ wq2_rptr[j]; 
            end 
        endgenerate 
    
    assign wbin_rbin_diff  = (wbinnext > wq2_rptr_bin) ? (wbinnext - wq2_rptr_bin) 
                                                        : (wq2_rptr_bin - wbinnext); 
    assign walmost_full_val = (wbin_rbin_diff >= ALMOST_FULL);
                                                    
    always @(posedge w_clk or posedge w_rst)
       begin
           if(w_rst) w_almost_full <= 0; 
           else      w_almost_full <= walmost_full_val;
       end                                                                                               
endmodule

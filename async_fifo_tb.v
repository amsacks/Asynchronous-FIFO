module async_fifo_tb
    #(  parameter WIDTH   = 5,
        parameter DEPTH   = 16,   
        parameter T_READ  = 40, // in ns
        parameter T_WRITE = 10 
     );
     
     reg                w_clk;
     reg                w_en;
     reg [WIDTH - 1:0]  in;
     wire               full;
     wire               almost_full;
     
     reg                r_clk; 
     reg                r_en; 
     wire [WIDTH - 1:0] out; 
     wire               empty;
     wire               almost_empty; 

    // Write clock
    always
        begin
            #(T_WRITE/2)
            w_clk <= (~w_clk);
        end          
    
    // Read clock
    always
        begin
            #(T_READ/2)
            r_clk <= (~r_clk);
        end
        
    reg rst;    
    reg r1_r_rst, r2_r_rst; 
    reg r1_w_rst, r2_w_rst;
    
    // Initialize input control signals to FIFO; issue a reset. 
    initial
        begin
            w_en   = 0;
            r_en   = 0;
            in     = {(WIDTH){1'b0}};
            w_clk  = 0;
            r_clk  = 0;
            rst    = 1;
            #(T_READ/4);       
            rst    = 0;
        end
        
  // Since using one reset (rst), need to synchronize the resets for both read/write clock domains
    always @(posedge r_clk or posedge rst)
        begin
            if(rst) {r2_r_rst, r1_r_rst} <= {2'b11};
            else    {r2_r_rst, r1_r_rst} <= {r1_r_rst, 1'b0};               
        end 
    always @(posedge w_clk or posedge rst)
        begin
            if(rst) {r2_w_rst, r1_w_rst} <= {2'b11};
            else    {r2_w_rst, r1_w_rst} <= {r1_w_rst, 1'b0}; 
        end 
    
    // Module under testing 
    async_fifo #( .DEPTH(DEPTH), .WIDTH(WIDTH))
    UUT
    (   .w_clk(w_clk                 ),
        .w_rst(r2_w_rst              ),
        .w_en(w_en                   ),
        .i_dat(in                    ),
        .w_full(full                 ),
        .w_almost_full(almost_full   ),
        
        .r_clk(r_clk                 ),
        .r_rst(r2_r_rst              ),
        .r_en(r_en                   ),
        .o_dat(out                   ),
        .r_empty(empty               ),
        .r_almost_empty(almost_empty )
     );   
    
    // Need a delay long enough such that the latency from synchronizing the resets
    // does not allow for any reset to be '1' while w_en is '1'. 
    // Whichever is larger (T_READ or T_WRITE)
    localparam DELAY  = 3*T_READ;
  
    // Begin Testing 
    initial
        begin: TB
            integer i;
            #(DELAY); 
            
            // Write to FIFO until full
            // Purposely Overfill. 
            w_en = 1;
            for(i = 0; i < DEPTH+5; i = i + 1)
                begin
                    @(posedge w_clk) 
                    in = i+7;  
                end 
            
            w_en = 0; 
            @(posedge w_clk);
            #(T_READ/2);
            r_en = 1; 
            
            // Read from FIFO until empty. 
            // Should not be able to read when empty. (i.e. Output stuck at 1st word) 
            for(i = 0; i < DEPTH+5; i = i + 1)
                begin
                    @(posedge r_clk)
                    ;               
                end  
        end // test bench 
endmodule   // async_fifo_tb.v

# Asynchronous-FIFO

An asynchronous FIFO buffer that allows for N entries, with empty/almost empty and full/almost full output status flags. Design heavily based off Clifford E. Cummings' work: http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf  
  
---    
# Resources Used  
  
  
  
# Testbench  
_FIFO parameters for testbench:_
  1. Depth is 16
  2. Data Width is 5 bits
  3. Almost Full is 8 
  4. Almost Empty is 8  
  
  The following test cases show that the FIFO buffer never gets overflowed or underflowed and confirms that the status flags are asserted immediately, but removed after a delay of 2-3 clock cycles.  
  
---  
**Test Case #1**: Only write to FIFO; try writing when FIFO is full. Check that the full/almost status flags are asserted immediately, and empty/almost empty flags are removed pessimesstically (delayed by the synchronizing of the write pointer to the read clock domain).   
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/async_fifo_tb_case1.png)  
  
The image shows the following: 
  - Immediately at 8 and 16 write clock cycles, the almost full and full flags are set HIGH, respectively. 
  - After a delay of 2-3 read clock cycles, the empty flag is set LOW and the almost empty flag is set HIGH. 
  
---  
**Test Case #2**: Only read from FIFO; try reading when FIFO is empty. Check that the empty/almost empty status flags are asserted immediately, and full/almost full flags are removed pessimesstically.    
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/async_fifo_tb_case2.png)  
  
The image shows the following:
  - After the first read clock cycle, the full flag is deasserted after a 2 write clock cycle delay.
  - The almost empty flag is deasserted after 2 read clock cycles after 8 reads have taken place (this is expected because of the synchronizing latency).
  - The almost full flag is deasserted after a delay.
  - The empty flag is asserted immediately at the 16th posedge of the read clock.
  - The FIFO was never overwritten in Test Case #1, since the last word in the FIFO is 22. 
  



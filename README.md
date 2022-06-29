# Asynchronous-FIFO

An asynchronous FIFO buffer that allows for N entries, with empty/almost empty and full/almost full output status flags. Design heavily based off Clifford E. Cummings' work: http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf  
  
# Testbench  
_FIFO parameters for testbench:_
  1. Depth is 16
  2. Data Width is 5 bits
  3. Almost Full is 8 
  4. Almost Empty is 8  
    
**Test Case #1**: Only write to FIFO; try writing when FIFO is full. Check that the full/almost status flags are correctly asserted, and the removal of empty/almost empty flags are removed pessimesstically (delayed by the synchronizing of the write pointer to the read clock domain).   
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/async_fifo_tb_case1.png)  
  
  After 16 write clock cycles with w_en HIGH and r_en LOW, the FIFO is full; the last word in the buffer is 22. Therefore, when reading from the FIFO in test case #2, 23 should never   appear



**Test Case #2**: Only read from FIFO. Check that the empty/almost empty status flags are correctly asserted, and the removal of full/almost empty flags are removed pessimesstically.  

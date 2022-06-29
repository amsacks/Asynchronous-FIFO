# Asynchronous-FIFO

An asynchronous FIFO buffer that allows for N entries, with empty/almost empty and full/almost full output status flags.  
Design heavily based off Clifford E. Cummings' work: http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf  
  
# Testbench

Test Case #1: Only write to FIFO; try writing when FIFO is full. Check that the full/almost status flags are correctly asserted, and the removal of empty/almost empty flags are removed pessimesstically (2-clock cycle delay). 
  
Test Case #2: Only read from FIFO. Check that the empty/almost empty status flags are correctly asserted, and the removal of full/almost empty flags are removed pessimesstically.  

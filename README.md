# Asynchronous FIFO

An asynchronous FIFO buffer that allows for N entries, with empty/almost empty and full/almost full output status flags. Design heavily based off Clifford E. Cummings' work: http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf  
  
   
# Resources Used  
Depth: 2^10 = 1024
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_resources.png)  
  
# Testbench  
_FIFO parameters for testbench:_
  1. Depth is 1024
  2. Data Width is 16 bits
  5. Read Clock 100 MHz 
  6. Write Clock 24 MHz
---  
  The following test cases show that the FIFO buffer never gets overflowed or underflowed and confirms that the status flags are asserted immediately, but removed after a delay of 2-3 clock cycles.  
  

**Test Case #1**: Only write to FIFO; try writing when FIFO is full. Check that the full/AF flags are asserted immediately, and empty/AE flags are removed pessimesstically.
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_deassert_AE_E_flags_W.png)
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_assert_AF_F_flags_W.png)

---
**Test Case #2**: Only read from FIFO. Check that full/AF flags are deasserted pessimesstically, and empty/AE flags are asserted immediately.
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_deassert_AF_F_flags_R.png)
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_assert_AE_E_flags_R.png)

---
**Test Case #3**: Write and read from FIFO. In this case read clock is faster than write clock, and both have no idle clock cycles. Then full/AF flags are never set, but rather empty flag cycles
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_assert_deassert_AF_F_flags_RW.png)
![image](https://github.com/amsacks/Asynchronous-FIFO/blob/main/tb/afifo_RCLK_greater_WCLK_never_F_AF_flags_when_RW.png)

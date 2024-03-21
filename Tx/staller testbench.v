module staller_tb ();
  reg i_stall_rst_n, i_stall_clk, i_stall_flag;
  reg [5:0] i_stall_cycles;
  wire o_stall_done, o_scl_stall;
  
parameter CLK_PERIOD = 20;
always #(CLK_PERIOD/2) i_stall_clk = ~i_stall_clk;

scl_staller DUT (
.i_stall_rst_n(i_stall_rst_n),
.i_stall_clk(i_stall_clk),
.i_stall_flag(i_stall_flag),
.i_stall_cycles(i_stall_cycles),
.o_stall_done(o_stall_done),
.o_scl_stall(o_scl_stall)
);

initial 
 begin
   i_stall_clk = 0;
   i_stall_rst_n = 0;
   i_stall_flag = 1;
   i_stall_cycles = 5;
   #(3*CLK_PERIOD);
   i_stall_rst_n = 1;
   @(o_stall_done);
   i_stall_flag = 0;
   #(3*CLK_PERIOD);
   $stop;
 end
 
 endmodule
   
   
   
   
   


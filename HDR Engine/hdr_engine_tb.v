`timescale 1us/1ns
module HDR_ENGINE_TB(); 
  reg sys_clk_tb=0,
      sys_rst_n_tb=0,
      i3cengine_hdrengine_en_tb,
      ccc_done_tb , 
      hdr_mode_done_tb,
      TOC_tb,
      CP_tb;
  reg [2:0] MODE_tb;
  wire i3cengine_hdrengine_done_tb, hdrmode_en_tb, ccc_en_tb;
parameter clk_period=10;

always #(clk_period/2) sys_clk_tb=~sys_clk_tb;
//DUT
hdr_engine DUT(

.i_sys_clk(sys_clk_tb),
.i_sys_rst_n(sys_rst_n_tb),
.i_i3cengine_hdrengine_en(i3cengine_hdrengine_en_tb),
.i_ccc_done(ccc_done_tb),
.i_hdr_mode_done(hdr_mode_done_tb),
.i_TOC(TOC_tb),
.i_CP(CP_tb),
.i_MODE(MODE_tb),
.o_i3cengine_hdrengine_done(i3cengine_hdrengine_done_tb),
.o_hdrmode_en(hdrmode_en_tb),
.o_ccc_en(ccc_en_tb));

//initial block
initial
begin
  //////////////first test case (CP=1//ccc_done=1)//////////////
//  #5
//  TOC_tb=1'b1;
//  MODE_tb=3'b110;
//sys_rst_n_tb=1'b0;
//#(clk_period);
//sys_rst_n_tb=1'b1;
//i3cengine_hdrengine_en_tb=1'b0;
//#3
//i3cengine_hdrengine_en_tb=1'b1;
//#3
//CP_tb=1'b1;
//#(5*clk_period);
//ccc_done_tb=1'b1;
///////////////////////second test case (CP=0//hdrmode_done=1)///////
//  #5
//  TOC_tb=1'b1;
//  MODE_tb=3'b110;
//sys_rst_n_tb=1'b0;
//#(clk_period);
//sys_rst_n_tb=1'b1;
//i3cengine_hdrengine_en_tb=1'b0;
//#3
//i3cengine_hdrengine_en_tb=1'b1;
//#3
//CP_tb=1'b0;
//#(5*clk_period);
//hdr_mode_done_tb=1'b1;
/////////////////////third test case ////////////
  #5
  TOC_tb=1'b1;
  MODE_tb=3'b110;
sys_rst_n_tb=1'b0;
#(clk_period);
sys_rst_n_tb=1'b1;
i3cengine_hdrengine_en_tb=1'b0;
#3
i3cengine_hdrengine_en_tb=1'b1;
#3
CP_tb=1'b0;
#(5*clk_period);
hdr_mode_done_tb=1'b1;
#(15*clk_period);
$stop;

end
endmodule

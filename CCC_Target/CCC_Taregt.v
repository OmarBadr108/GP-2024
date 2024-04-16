module CCC_Target(

input wire        i_sys_clk ,
input wire        i_sys_rst ,
input wire        i_engine_en ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire 		  i_exit_done ,
input wire		  i_restart_done ,
inpur wire 		  i_RnW ,
input wire [15:0] i_regf_MWL ,
input wire [15:0] i_regf_MRL ,
input wire [7:0]  i_CCC_value ,
input wire [7:0]  i_Def_byte ,
input wire        i_rx_error

output reg 		  o_tx_en ,
output reg [2:0]  o_tx_mode ,
output reg 		  o_rx_en ,
output reg [2:0]  o_rx_mode ,
output reg 		  o_engine_done ,
output reg [7:0]  o_regf_addr ,
output reg 		  o_wr_en ,
output reg 		  o_rd_en 








);
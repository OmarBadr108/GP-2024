module Target_engine (
	input wire 		 i_sys_clk ,
	input wire 		 i_sys_rst ,
	input wire 		 i_rstdet_RESTART , 
	input wire 		 i_exitdet_EXIT ,
	input wire 		 i_ENTHDR_done ,
	input wire  	 i_rx_CCC_done ,
	input wire 		 i_rx_NT_done ,
	input wire [1:0] i_rx_dec ,
	input wire 		 i_rx_dec_done ,



	output reg 		 o_ENTHDR_en ,
	output reg 		 o_NT_en ,
	output reg 	     o_CCC_en ,
	output reg 	 	 o_rx_en ,
	output reg [3:0] o_rx_mode  
);
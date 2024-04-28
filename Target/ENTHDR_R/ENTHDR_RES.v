module ENTHDR_RES (
	input wire i_sys_clk ,
	input wire i_sys_rst ,
	input wire i_enigne_en , 
	input wire i_sda ,
	input wire i_scl ,

	output reg o_sdahnd_sda ,
	output reg o_engine_done 
);
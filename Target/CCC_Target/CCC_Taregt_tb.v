module CCC_Taregt_tb ();
	reg i_sys_clk_tb,    
		i_sys_rst_tb,
		i_engine_en_tb,
		i_tx_mode_done_tb,
		i_rx_mode_done_tb,
		i_exit_done_tb,
		i_restart_done_tb,
		i_RnW_tb,
		i_rx_error_tb,
		premable_tb;
	reg [15:0] i_regf_MWL_tb,i_regf_MRL_tb;
	reg [7:1] i_CCC_value_tb,i_Def_byte_tb;
	wire o_tx_en_tb , o_rx_en_tb , o_engine_done_tb,o_regf_wr_en_tb,o_regf_rd_en_tb;
	wire [4:0] o_tx_mode_tb, o_rx_mode_tb;
	wire [7:0] o_regf_addr_tb;

	

parameter clk_period=10;

always #(clk_period/2) i_sys_clk_tb=~i_sys_clk_tb;

//DUT
CCC_Target DUT(
.i_sys_clk(i_sys_clk_tb),
.i_sys_rst(i_sys_rst_tb),
.i_engine_en(i_engine_en_tb),
.i_tx_mode_done(i_tx_mode_done_tb),
.i_rx_mode_done(i_rx_mode_done_tb),
.i_exit_done(i_exit_done_tb),
.i_restart_done(i_restart_done_tb),
.i_RnW(i_RnW_tb),
.i_rx_error(i_rx_error_tb),
.premable(premable_tb),
.i_regf_MWL(i_regf_MWL_tb),
.i_regf_MRL(i_regf_MRL_tb),
.i_CCC_value(i_CCC_value_tb),
.i_Def_byte(i_Def_byte_tb),
.o_tx_en(o_tx_en_tb),
.o_rx_en(o_rx_en_tb),
.o_engine_done(o_engine_done_tb),
.o_regf_wr_en(o_regf_wr_en_tb),
.o_regf_rd_en(o_regf_rd_en_tb),
.o_tx_mode(o_tx_mode_tb),
.o_rx_mode(o_rx_mode_tb),
.o_regf_addr(o_regf_addr_tb));




endmodule

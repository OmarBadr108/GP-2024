module CCC_Taregt_tb ();
	reg i_sys_clk_tb=1'b0,    
		i_sys_rst_tb,
		i_engine_en_tb,
		//i_tx_mode_done_tb,
		//i_rx_mode_done_tb,
		i_exit_done_tb,
		i_restart_done_tb,
		//i_RnW_tb;
	//wire i_rx_error_tb;
	reg [15:0] i_regf_MWL_tb,i_regf_MRL_tb;
	reg [7:1] i_CCC_value_tb,i_Def_byte_tb;
	wire o_tx_en_tb , o_rx_en_tb , o_engine_done_tb,o_regf_wr_en_tb,o_regf_rd_en_tb,o_detector_en_tb;
	wire [2:0] o_tx_mode_tb;
	wire [3:0] o_rx_mode_tb;
	wire [7:0] o_regf_addr_tb;
	wire tx_mode_done_tb , o_ddrccc_rx_mode_done_tb, o_ddrccc_pre_tb,o_ddrccc_error_tb,i_rx_ddrccc_rnw_tb;

	

parameter clk_period=10;

//////////////CLK_GENERATOR////////////
always #(clk_period/2) i_sys_clk_tb=~i_sys_clk_tb;

//DUT
CCC_Target DUT(
.i_sys_clk(i_sys_clk_tb),
.i_sys_rst(i_sys_rst_tb),
.i_engine_en(i_engine_en_tb),
.i_tx_mode_done(tx_mode_done_tb),
.i_rx_mode_done(o_ddrccc_rx_mode_done_tb),
.i_exit_done(i_exit_done_tb),
.i_restart_done(i_restart_done_tb),
.i_RnW(i_rx_ddrccc_rnw_tb),
.i_rx_error(o_ddrccc_error_tb),
.premable(o_ddrccc_pre_tb),
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
.o_regf_addr(o_regf_addr_tb),
.o_detector_en(o_detector_en_tb));

////////SCL_GENERETION////
reg i_scl_gen_stall_tb, i_timer_cas_tb, i_sdr_ctrl_scl_idle_tb;
wire i_sclgen_scl_tb;
	
scl_generation DUT3 (
    .i_sdr_ctrl_clk     	(i_sys_clk_tb),
    .i_sdr_ctrl_rst_n   	(i_sys_rst_tb),
    .i_sdr_scl_gen_pp_od	(i_sdr_scl_gen_pp_od_tb), 	
    .i_scl_gen_stall    	(i_scl_gen_stall_tb),   
    .i_sdr_ctrl_scl_idle	(i_sdr_ctrl_scl_idle_tb),
    .i_timer_cas        	(i_timer_cas_tb), 	
    .o_scl_pos_edge     	(i_sclgen_scl_pos_edge_tb),
    .o_scl_neg_edge     	(i_sclgen_scl_neg_edge_tb),
    .o_scl              	(i_sclgen_scl_tb)                         	
);
////////RX_BLOCK///////
reg i_sdahnd_rx_sda_tb;
reg [4:0] i_crc_value_tb = 5'b11010;
wire [7:0] o_regfcrc_rx_data_out_tb, o_ccc_ccc_value_tb;
wire [1:0] o_engine_decision_tb;
wire [3:0]  o_rx_mode_tb;
target_rx DUT4 (
	.i_sys_clk					(i_sys_clk_tb)				,
	.i_sys_rst					(i_sys_rst_tb)				,
	.i_sclgen_scl				(i_sclgen_scl_tb)			,
	.i_sclgen_scl_pos_edge		(i_sclgen_scl_pos_edge_tb)	,
	.i_sclgen_scl_neg_edge		(i_sclgen_scl_neg_edge_tb)	,
	.i_ddrccc_rx_en				(o_rx_en_tb)			,
	.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
	.i_ddrccc_rx_mode			(o_rx_mode_tb)		,
	.i_crc_value 				(i_crc_value_tb),		
	.o_regfcrc_rx_data_out		(o_regfcrc_rx_data_out_tb)	,
	.o_ddrccc_rx_mode_done		(o_ddrccc_rx_mode_done_tb)	,
	.o_ddrccc_pre				(o_ddrccc_pre_tb)			,
	.o_ddrccc_error_flag		(o_ddrccc_error_tb)			,
	.o_ddrccc_rnw   			(i_rx_ddrccc_rnw_tb)  ,
	.o_engine_decision 			(o_engine_decision_tb) ,
	.o_ccc_ccc_value 			(o_ccc_ccc_value_tb)      
);
/////////////////TX_BLOCK/////////////
reg [7:0] i_regf_tx_parallel_data_tb ;
wire o_sdahnd_tgt_serial_data_tb, o_crc_en_tb;
wire [7:0] o_crc_parallel_data_tb;

tx_t  DUT5(
   .i_sys_clk_tb				(i_sys_clk_tb),
   .i_sys_rst_tb				(i_sys_rst_tb),
   .i_sclgen_scl 				(i_sclgen_scl_tb),
   .i_sclgen_scl_pos_edge 		(i_sclgen_scl_pos_edge_tb),
   .i_sclgen_scl_neg_edge 		(i_sclgen_scl_neg_edge_tb),
   .i_ddrccc_tx_en 				(o_tx_en_tb),
   .i_ddrccc_tx_mode 			(o_tx_mode_tb),
   .i_regf_tx_parallel_data 	(i_regf_tx_parallel_data_tb),
   .i_crc_crc_value 			(i_crc_value_tb),
   .o_sdahnd_tgt_serial_data 	(o_sdahnd_tgt_serial_data_tb),
   .o_ddrccc_tx_mode_done 		(tx_mode_done_tb),
   .o_crc_en 					(o_crc_en_tb), 
   .o_crc_parallel_data 		(o_crc_parallel_data_tb)
);
//initial block
initial
begin










endmodule
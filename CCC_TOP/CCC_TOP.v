module CCC_TOP (
	// ports are :
	// any thing related to i3c Engine and CRC and ddr are temporarly considered as ports 
	// system signals like clk and rst and sclgen rst 
	// and of course SDA and SCL

	input 		sys_clk = 0 ,
	input 		rst_n ,
	input 	 	i3cengine_hdrengine_en ,
	input   	i_sclgen_rst_n_tb ,
	input  		ddr_mode_done_tb ,
	input 		TOC_tb ,
	input 		CP_tb ,
	input 		i_MODE ,
	input [4:0] i_crc_crc_value_tb ,
	input [7:0] o_crc_parallel_data_tb ,

	output reg ddrmode_en_tb ,
	output reg i3cengine_hdrengine_done_tb ,
	output reg regf_addr_special_tb ,

	);


///////////////////////// scl generation ///////////////////////////////
	wire 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb  ;
	wire  	   SCL ;

	////////////////////////// bits counter //////////////////////////////// 
	wire  	   i_bitcnt_en_tb ;
	wire [5:0] o_cnt_bit_count_tb ;
	wire  	   o_bitcnt_err_rst_tb ;
	/////////////////////////// CCC Handler /////////////////////////////
	wire       engine_ccc_en  ,i_sclstall_stall_done_tb  ;
	wire       i_frmcnt_last_frame_tb ;
	wire   	   o_frmcnt_Direct_Broadcast_n_tb ;
	// related to tx
	wire	   i_tx_mode_done_tb ,o_tx_en_tb ;
	wire [3:0] o_tx_mode_tb ;
 	// related to rx
	wire	   i_rx_mode_done_tb ,i_rx_pre_tb ,i_rx_error_tb ,o_rx_en_tb ;
	wire [3:0] o_rx_mode_tb ;
	// related to regfile (configuration)


	wire 	    i_regf_RnW_tb ,i_regf_TOC_tb , i_regf_WROC_tb , i_regf_DBP_tb , i_regf_SRE_tb ;
	wire [2:0]  i_regf_CMD_ATTR_tb ;
	wire [7:0]  i_regf_CMD_tb ;
	wire [4:0]  i_regf_DEV_INDEX_tb ;
	wire [2:0]  i_regf_DTT_tb ;
	wire  	    o_regf_wr_en_tb , o_regf_rd_en_tb ;
	wire [11:0] o_regf_addr_tb ; 	 	 	// this may be changed 
	wire  	    ccc_engine_done ;
	wire [7:0]  o_txrx_addr_ccc_tb ;
	wire   	    o_engine_odd_tb ;
	wire [3:0]  o_regf_ERR_STATUS_tb ;
	// related to scl staller 
	wire 	   o_sclstall_en_tb ;
	wire [4:0] i_stall_cycles ;

	//related to frame counter
	wire 	   o_frmcnt_en_tb ;


	wire       SDA ;
	wire ddr_mode_done_tb ; // temporary 

	hdr_engine hdr_engine(

		.i_sys_clk(sys_clk),
		.i_sys_rst_n(rst_n),

		.i_i3cengine_hdrengine_en(i3cengine_hdrengine_en),
		.i_ccc_done(ccc_engine_done),
		.i_ddr_mode_done(ddr_mode_done_tb),
		.i_TOC(TOC_tb),
		.i_CP(CP_tb),
		.i_MODE(i_MODE),
		.o_i3cengine_hdrengine_done(i3cengine_hdrengine_done_tb),
		.o_ddrmode_en(ddrmode_en_tb),
		.o_ccc_en(engine_ccc_en),
		.o_regf_addr_special(regf_addr_special_tb)
		// o_engine_odd is missing
		);




	CCC_Handler CCC_Handler (
		.i_sys_clk	            (sys_clk),
		.i_sys_rst			    (rst_n),
															.i_engine_en 			(engine_ccc_en),
		.i_bitcnt_number		(o_cnt_bit_count_tb),
		.i_tx_mode_done 		(i_tx_mode_done_tb),
		.i_rx_mode_done 		(i_rx_mode_done_tb),
		.i_rx_pre 				(i_rx_pre_tb),
		.i_sclstall_stall_done  (i_sclstall_stall_done_tb),
		.i_rx_error 	 	    (i_rx_error_tb),
		.i_frmcnt_last_frame 	(i_frmcnt_last_frame_tb),

		.i_i_regf_RnW       (i_regf_RnW_tb),
		.i_i_regf_CMD_ATTR  (i_regf_CMD_ATTR_tb),
		.i_i_regf_CMD       (i_regf_CMD_tb),
		.i_i_regf_DEV_INDEX (i_regf_DEV_INDEX_tb),
		.i_i_regf_TOC       (i_regf_TOC_tb),
		.i_i_regf_WROC      (i_regf_WROC_tb),
		.i_i_regf_DTT       (i_regf_DTT_tb),
		.i_i_regf_DBP       (i_regf_DBP_tb),
		.i_i_regf_SRE       (i_regf_SRE_tb),
		
		.o_sclstall_en(o_sclstall_en_tb),
		.o_sclstall_code(i_stall_cycles),
		.o_tx_en(o_tx_en_tb),
		.o_tx_mode(o_tx_mode_tb),
		.o_rx_en(o_rx_en_tb),
		.o_rx_mode(o_rx_mode_tb),
		.o_bitcnt_en(i_bitcnt_en_tb),
		.o_bitcnt_err_rst(o_bitcnt_err_rst_tb),
		.o_frmcnt_en(o_frmcnt_en_tb),
		.o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb), 	 	 	 	 	 	 // 

		.o_frmcnt_Direct_Broadcast_n(o_frmcnt_Direct_Broadcast_n_tb),

		.o_regf_wr_en(o_regf_wr_en_tb),
		.o_regf_rd_en(o_regf_rd_en_tb),
		.o_regf_addr(o_regf_addr_tb),
														.o_engine_done(ccc_engine_done),
		.o_txrx_addr_ccc(o_txrx_addr_ccc_tb),
														.o_engine_odd(o_engine_odd_tb),
		.o_regf_ERR_STATUS(o_regf_ERR_STATUS_tb)
		);




	scl_generation scl_generation (
		.i_sdr_ctrl_clk      (sys_clk),
		.i_sdr_ctrl_rst_n 	 (i_sclgen_rst_n_tb),
		.i_sdr_scl_gen_pp_od (i_sdr_scl_gen_pp_od_tb),
		.i_scl_gen_stall  	 (i_scl_gen_stall_tb),
		.i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb),
		.i_timer_cas         (i_timer_cas_tb),
		.o_scl_pos_edge      (scl_pos_edge_tb),
		.o_scl_neg_edge      (scl_neg_edge_tb),
		.o_scl 	 			 (SCL)

	);

		wire  		 o_frcnt_toggle_tb ;


		bits_counter bits_counter (
		.i_sys_clk       (sys_clk),
		.i_rst_n 	     (rst_n),
		.i_bitcnt_en     (i_bitcnt_en_tb),
		.i_scl_pos_edge  (scl_pos_edge_tb),
		.i_scl_neg_edge  (scl_neg_edge_tb),
		.i_cccnt_err_rst (o_bitcnt_err_rst_tb),
		.o_frcnt_toggle  (o_frcnt_toggle_tb),
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);

		reg  [15:0]	i_regf_DATA_LEN_tb ;
		wire    	i_fcnt_no_frms_tb ;
		wire 	 	i_fcnt_en_tb ;
		wire  	 	o_fcnt_last_frame_tb ;
		


		frame_counter frame_counter (
		//.i_fcnt_no_frms (i_fcnt_no_frms_tb),
		.i_fcnt_clk (sys_clk),
		.i_fcnt_rst_n (rst_n),
		.i_fcnt_en (o_frmcnt_en_tb),
		.i_regf_CMD_ATTR (i_regf_CMD_ATTR_tb[0]),
		.i_regf_DATA_LEN (i_regf_DATA_LEN_tb),
		.i_regf_DTT (i_regf_DTT_tb),
		.i_cnt_bit_count (o_cnt_bit_count_tb),
		.i_ccc_Direct_Broadcast_n(o_frmcnt_Direct_Broadcast_n_tb), // 
		.i_scl_pos_edge (scl_pos_edge_tb),
		.i_scl_neg_edge(scl_neg_edge_tb),
		.i_bitcnt_toggle(o_frcnt_toggle_tb),
		//.o_fcnt_last_frame (o_fcnt_last_frame_tb)
		.o_cccnt_last_frame (i_frmcnt_last_frame_tb)	 	 		 	 

	);
		wire o_scl_stall_tb ; // mesh mohem at the moment
		 
		 scl_staller scl_staller (
		 .i_stall_clk(sys_clk), 
		 .i_stall_rst_n(rst_n),
		 .i_stall_flag(o_sclstall_en_tb),
		 .i_stall_cycles(i_stall_cycles),
		 .o_stall_done(i_sclstall_stall_done_tb),
		 .o_scl_stall(o_scl_stall_tb)
    );


		 wire [7:0]  i_regf_data_wr_tb ;
		 reg  [11:0] i_engine_configuration_tb ;
		 wire [3:0]  o_engine_TID_tb ;
		 wire [2:0]  o_engine_MODE_tb ;
		 wire        o_engine_CP_tb ;
		 wire [7:0]  i_regf_tx_parallel_data_tb ;

		 //////////////////////////////////////// for testing only /////////////////////////////////////////// 
		 reg 		  my_regf_wr_en_tb ;
		 reg  	 	  my_regf_wr_en_tb_selector ;
		 wire  	 	  my_regf_wr_en_tb_mux_out ;

		 reg  [7:0]   my_regf_data_wr_tb ;
		 reg 	 	  my_regf_data_wr_tb_selector ;
		 wire [7:0]	  my_regf_data_wr_tb_mux_out ;

		 reg  [11:0]  my_regf_addr_tb ;
		 reg 	 	  my_regf_addr_tb_selector ;
		 wire [11:0]  my_regf_addr_tb_mux_out ;

		 
		 reg_file reg_file (
		.i_regf_clk(sys_clk),
		.i_regf_rst_n(rst_n),
		.i_regf_rd_en(o_regf_rd_en_tb),
		.i_regf_wr_en(my_regf_wr_en_tb_mux_out), 	 	 	// muxed 
		.i_regf_data_wr(my_regf_data_wr_tb_mux_out),        // muxed with rx 
		.i_regf_addr(my_regf_addr_tb_mux_out),				// muxed 
		.i_engine_configuration(i_engine_configuration_tb),

		.o_frmcnt_data_len(i_regf_DATA_LEN_tb),
		.o_cccnt_CMD_ATTR(i_regf_CMD_ATTR_tb),
		.o_engine_TID(o_engine_TID_tb),
		.o_ccc_CMD(i_regf_CMD_tb),
		.o_cccnt_DEV_INDEX(i_regf_DEV_INDEX_tb),
		.o_frmcnt_DTT(i_regf_DTT_tb),
		.o_engine_MODE(o_engine_MODE_tb), // with engine 
		.o_cccnt_RnW(i_regf_RnW_tb),
		.o_cccnt_WROC(i_regf_WROC_tb),
		.o_cccnt_TOC(i_regf_TOC_tb),
		.o_cccnt_DBP(i_regf_DBP_tb),
		.o_cccnt_SRE(i_regf_SRE_tb),
		.o_engine_CP(o_engine_CP_tb),

		.o_ser_rx_tx(),
		.o_regf_data_rd(i_regf_tx_parallel_data_tb),
		.o_regf_num_frames(),
		.o_crh_CRHDLY(),
		.o_crh_getstatus_data(),
		.o_crh_CRCAP2(),
		.o_crh_PRECR(),
		.o_crh_cfg_reg(),
		.o_crh_tgts_count(),
		.o_regf_ibi_cfg(),
		.o_regf_ibi_payload_size_reg(),
		.o_i_ibi_tgt_address(),
		.o_regf_hj_cfg(),
		.o_regf_hj_support()

		);

/*	
		mux  #(.WIDTH(1)) mux_1 (
			.i_mux_one(my_regf_wr_en_tb),
			.i_mux_zero(o_regf_wr_en_tb),
			.i_selector(my_regf_wr_en_tb_selector),
			.o_mux_out(my_regf_wr_en_tb_mux_out)
			);

		mux #(.WIDTH(8)) mux_2  (
			.i_mux_one(my_regf_data_wr_tb),
			.i_mux_zero(i_regf_data_wr_tb),
			.i_selector(my_regf_data_wr_tb_selector),
			.o_mux_out(my_regf_data_wr_tb_mux_out)
			);

		mux  #(.WIDTH(12)) mux_3 (
			.i_mux_one(my_regf_addr_tb),
			.i_mux_zero(o_regf_addr_tb),
			.i_selector(my_regf_addr_tb_selector),
			.o_mux_out(my_regf_addr_tb_mux_out)
			);
*/

		reg       i_sdahnd_rx_sda_tb ;
		reg 	  i_crc_value_tb ;
		reg  	  i_crc_valid_tb ;
		wire      o_crc_data_valid_tb ;
		wire  	  o_ddrccc_error_done_tb ;
		wire  	  o_crc_en_tb ;

		RX RX (
		.i_sys_clk					(sys_clk)				,
		.i_sys_rst					(rst_n)				,
		.i_sclgen_scl				(SCL)					,
		.i_sclgen_scl_pos_edge		(scl_pos_edge_tb)			,
		.i_sclgen_scl_neg_edge		(scl_neg_edge_tb)			,
		.i_ddrccc_rx_en				(o_rx_en_tb)				,
		.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
		//.i_bitcnt_rx_bit_count 	(i_bitcnt_rx_bit_count_tb)	,
		.i_ddrccc_rx_mode			(o_rx_mode_tb)				,
		.i_crc_value				(i_crc_value_tb)			,
		.i_crc_valid				(i_crc_valid_tb)			,
			
		.o_regfcrc_rx_data_out		(i_regf_data_wr_tb)			,
		.o_ddrccc_rx_mode_done		(i_rx_mode_done_tb)			,
		.o_ddrccc_pre				(i_rx_pre_tb)				,
		.o_ddrccc_error				(i_rx_error_tb)				,
		.o_crc_en					(o_crc_en_tb)               , // 
		.o_crc_data_valid           (o_crc_data_valid_tb)       ,
		.o_ddrccc_error_done   	    (o_ddrccc_error_done_tb)      

);

    	tx tx (
		.i_sys_clk 				 (sys_clk),
		.i_sys_rst 				 (rst_n),
		.i_ddrccc_tx_en 		 (o_tx_en_tb),
		.i_sclgen_scl_pos_edge 	 (scl_pos_edge_tb),
		.i_sclgen_scl_neg_edge 	 (scl_neg_edge_tb),
		.i_ddrccc_tx_mode 		 (o_tx_mode_tb),
		.i_regf_tx_parallel_data (i_regf_tx_parallel_data_tb),
		.i_ddrccc_special_data 	 (i_regf_CMD_tb),
		.i_crc_crc_value 		 (i_crc_crc_value_tb),
		.o_sdahnd_serial_data 	 (SDA),
		.o_ddrccc_mode_done 	 (i_tx_mode_done_tb),
		.o_crc_parallel_data 	 (o_crc_parallel_data_tb),
		.o_crc_en 				 (o_crc_en_tb)
);

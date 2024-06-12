import CCC_HANDLER_PACKAGE ::*;

module CCC_Handler_tb ();


// 1-signal declaration 
	
	// common signals 
	reg        i_sys_clk_tb = 0 , i_rst_n_tb  ;

	///////////////////////// scl generation ///////////////////////////////
	reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb , o_scl_tb ;

	////////////////////////// bits counter //////////////////////////////// 
	reg  	   i_bitcnt_en_tb ;
	wire [5:0] o_cnt_bit_count_tb ;
	wire  	   o_bitcnt_err_rst_tb ;
	/////////////////////////// CCC Handler /////////////////////////////
	reg        i_engine_en_tb  ,i_sclstall_stall_done_tb  ;
	wire       i_frmcnt_last_frame_tb ;
	wire   	   o_frmcnt_Direct_Broadcast_n_tb ;
	// related to tx
	reg 	   i_tx_mode_done_tb ,o_tx_en_tb ;
	reg  [3:0] o_tx_mode_tb ;
 	// related to rx
	reg 	   i_rx_mode_done_tb ,i_rx_pre_tb ,i_rx_error_tb ,o_rx_en_tb ;
	reg  [3:0] o_rx_mode_tb ;

	// new /////
	wire  en_mux ;
	////////////
	// related to regfile (configuration)


	reg  	    i_regf_RnW_tb ,i_regf_TOC_tb , i_regf_WROC_tb , i_regf_DBP_tb , i_regf_SRE_tb ;
	reg  [2:0]  i_regf_CMD_ATTR_tb ;
	reg  [7:0]  i_regf_CMD_tb ;
	reg  [4:0]  i_regf_DEV_INDEX_tb ;
	reg  [2:0]  i_regf_DTT_tb ;
	wire  	    o_regf_wr_en_tb , o_regf_rd_en_tb ;
	wire [11:0] o_regf_addr_tb ; 	 	 	// this may be changed 
	wire  	    o_engine_done_tb ;
	wire [7:0]  o_txrx_addr_ccc_tb ;
	wire   	    o_engine_odd_tb ;
	wire [3:0]  o_regf_ERR_STATUS_tb ;
	// related to scl staller 
	wire 	   o_sclstall_en_tb ;
	wire [4:0] i_stall_cycles ;

	//related to frame counter
	wire 	   o_frmcnt_en_tb ;

	///////////////// scl gen ////////////////////

	
	reg i_sclgen_rst_n_tb ;

// 2-clk generation 
	
	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;

	// scl ddr clk = 25 Mhz
	parameter DDR_CLK_PERIOD = 40 ;

// 3-DUT instatiation 
	

	CCC_Handler CCC_Handler_dut (
		.i_sys_clk	            (i_sys_clk_tb),
		.i_sys_rst			    (i_rst_n_tb),
		.i_engine_en 			(i_engine_en_tb),
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
		//.i_regf_DATA_LENGTH(),
		.o_sclstall_en(o_sclstall_en_tb),
		.o_sclstall_code(i_stall_cycles),
		.o_tx_en(o_tx_en_tb),
		.o_tx_mode(o_tx_mode_tb),
		.o_rx_en(o_rx_en_tb),
		.o_rx_mode(o_rx_mode_tb),
		.o_bitcnt_en(i_bitcnt_en_tb),
		.o_bitcnt_err_rst(o_bitcnt_err_rst_tb),
		.o_frmcnt_en(o_frmcnt_en_tb),
		.o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb), 	 	 	 	 	 	  

		.o_frmcnt_Direct_Broadcast_n(o_frmcnt_Direct_Broadcast_n_tb),

		.o_regf_wr_en(o_regf_wr_en_tb),
		.o_regf_rd_en(o_regf_rd_en_tb),
		.o_regf_addr(o_regf_addr_tb),
		.o_engine_done(o_engine_done_tb),
		.o_txrx_addr_ccc(o_txrx_addr_ccc_tb),
		.o_engine_odd(o_engine_odd_tb),
		.o_regf_ERR_STATUS(o_regf_ERR_STATUS_tb),

		.o_en_mux(en_mux)       // new
		);


	scl_generation scl_gen_dut (
		.i_sdr_ctrl_clk      (i_sys_clk_tb),
		.i_sdr_ctrl_rst_n 	 (i_sclgen_rst_n_tb),
		.i_sdr_scl_gen_pp_od (i_sdr_scl_gen_pp_od_tb),
		.i_scl_gen_stall  	 (i_scl_gen_stall_tb),
		.i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb),
		.i_timer_cas         (i_timer_cas_tb),
		.o_scl_pos_edge      (scl_pos_edge_tb),
		.o_scl_neg_edge      (scl_neg_edge_tb),
		.o_scl 	 			 (o_scl_tb)

	);

		wire  		 o_frcnt_toggle_tb ;


		bits_counter bits_counter_dut (
		.i_sys_clk       (i_sys_clk_tb),
		.i_rst_n 	     (i_rst_n_tb),
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
		


		frame_counter frame_counter_dut (
		.i_fcnt_clk (i_sys_clk_tb),
		.i_fcnt_rst_n (i_rst_n_tb),
		.i_fcnt_en (o_frmcnt_en_tb),
		.i_regf_CMD_ATTR (i_regf_CMD_ATTR_tb[0]),
		.i_regf_DATA_LEN (i_regf_DATA_LEN_tb),
		.i_regf_DTT (i_regf_DTT_tb),
		.i_cnt_bit_count (o_cnt_bit_count_tb),
		.i_bitcnt_toggle(o_frcnt_toggle_tb),
		.o_cccnt_last_frame (i_frmcnt_last_frame_tb)	 	 		 	 

	);
		wire o_scl_stall_tb ; // mesh mohem at the moment
		 
		 scl_staller scl_staller_dut (
		 .i_stall_clk(i_sys_clk_tb), 
		 .i_stall_rst_n(i_rst_n_tb),
		 .i_stall_flag(o_sclstall_en_tb),
		 .i_stall_cycles(i_stall_cycles),
		 .o_stall_done(i_sclstall_stall_done_tb),
		 .o_scl_stall(o_scl_stall_tb)
    );


		 wire [7:0]  i_rx_regfcrc_data_wr_tb ;
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

		 
		 reg_file reg_file_dut (
		.i_regf_clk(i_sys_clk_tb),
		.i_regf_rst_n(i_rst_n_tb),
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

	
		mux  #(.WIDTH(1)) DUT6 (
			.i_mux_one(my_regf_wr_en_tb),
			.i_mux_zero(o_regf_wr_en_tb),
			.i_selector(my_regf_wr_en_tb_selector),
			.o_mux_out(my_regf_wr_en_tb_mux_out)
			);

		mux #(.WIDTH(8)) DUT7  (
			.i_mux_one(my_regf_data_wr_tb),
			.i_mux_zero(i_rx_regfcrc_data_wr_tb),
			.i_selector(my_regf_data_wr_tb_selector),
			.o_mux_out(my_regf_data_wr_tb_mux_out)
			);

		mux  #(.WIDTH(12)) DUT8 (
			.i_mux_one(my_regf_addr_tb),
			.i_mux_zero(o_regf_addr_tb),
			.i_selector(my_regf_addr_tb_selector),
			.o_mux_out(my_regf_addr_tb_mux_out)
			);


		reg        i_sdahnd_rx_sda_tb ;
		wire [4:0] i_crc_value_tb ;
		wire  	   i_crc_valid_tb ;
		wire       o_crc_data_valid_tx_tb ;
		wire       o_crc_data_valid_rx_tb ;
		wire  	   o_ddrccc_error_done_tb ;
		wire  	   o_crc_en_tb ;
		wire 	   o_crc_last_byte_tx_tb ;
		wire 	   o_crc_last_byte_rx_tb ; // to be connected

		wire       o_sdahnd_serial_data_tb ;
    	wire [7:0] o_crc_parallel_data_tx_tb ;
    	//wire [7:0] o_crc_parallel_data_rx_tb ; already declared as : i_rx_regfcrc_data_wr_tb

		rx rx_dut (
		.i_sys_clk					(i_sys_clk_tb)				,
		.i_sys_rst					(i_rst_n_tb)				,
		.i_sclgen_scl				(o_scl_tb)					,
		.i_sclgen_scl_pos_edge		(scl_pos_edge_tb)			,
		.i_sclgen_scl_neg_edge		(scl_neg_edge_tb)			,
		.i_ddrccc_rx_en				(o_rx_en_tb)				,
		.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
		//.i_bitcnt_rx_bit_count 	(i_bitcnt_rx_bit_count_tb)	,
		.i_ddrccc_rx_mode			(o_rx_mode_tb)				,
		.i_crc_value				(i_crc_value_tb)			,
		.i_crc_valid				(i_crc_valid_tb)			,
			
		.o_regfcrc_rx_data_out		(i_rx_regfcrc_data_wr_tb)			,
		.o_ddrccc_rx_mode_done		(i_rx_mode_done_tb)			,
		.o_ddrccc_pre				(i_rx_pre_tb)				,
		.o_ddrccc_error				(i_rx_error_tb)				,
		.o_crc_en					(crc_en_rx)                 , // 
		.o_crc_data_valid           (o_crc_data_valid_rx_tb)    ,
		.o_crc_last_byte 			(o_crc_last_byte_rx_tb)
		//.o_ddrccc_error_done   	    (o_ddrccc_error_done_tb)      

);
    	
    

    	tx tx_dut (
		.i_sys_clk 				 (i_sys_clk_tb),
		.i_sys_rst 				 (i_rst_n_tb),

		.i_ddrccc_tx_en 		 (o_tx_en_tb),
		.i_sclgen_scl_pos_edge 	 (scl_pos_edge_tb),
		.i_sclgen_scl_neg_edge 	 (scl_neg_edge_tb),
		.i_ddrccc_tx_mode 		 (o_tx_mode_tb),

		.i_regf_tx_parallel_data (i_regf_tx_parallel_data_tb),
		.i_ddrccc_special_data 	 (o_txrx_addr_ccc_tb),
		.i_crc_crc_value 		 (i_crc_value_tb),
		.i_crc_data_valid  	  	 (i_crc_valid_tb), // new 
		.i_regf_read_n_write_bit (i_regf_RnW_tb), // new
		.o_sdahnd_serial_data 	 (o_sdahnd_serial_data_tb),
		.o_ddrccc_mode_done 	 (i_tx_mode_done_tb),
		.o_crc_parallel_data 	 (o_crc_parallel_data_tx_tb),
		.o_crc_en 				 (crc_en_tx) ,
		.o_crc_last_byte 		 (o_crc_last_byte_tx_tb), // new
		.o_crc_data_valid 		 (o_crc_data_valid_tx_tb)	// new
);

    wire 		mux1_out1 ;
    wire 		mux1_out2 ;
    wire 		mux1_out3 ;
    wire [7:0]  mux8_out  ;

    

	crc crc_dut (
	.i_sys_clk(i_sys_clk_tb),
    .i_sys_rst(i_rst_n_tb),
    .i_txrx_en(mux1_out1),
	.i_txrx_data_valid(mux1_out3),
	.i_txrx_last_byte(mux1_out2),
	.i_txrx_data(mux8_out),
	.o_txrx_crc_value(i_crc_value_tb),
	.o_txrx_crc_valid (i_crc_valid_tb)

);


mux1      mux1_1 (
	.en(en_mux),
	.tx(crc_en_tx),
	.rx(crc_en_rx),
	.y(mux1_out1)
	
);

mux1      mux1_2 (
	.en(en_mux),
	.tx(o_crc_last_byte_tx_tb),
	.rx(o_crc_last_byte_rx_tb),
	.y(mux1_out2)
	
);


mux1      mux1_3 (
	.en(en_mux),
	.tx(o_crc_data_valid_tx_tb),
	.rx(o_crc_data_valid_rx_tb),
	.y(mux1_out3)
	
);


mux8      mux1_8 (
	.en(en_mux),
	.tx(o_crc_parallel_data_tx_tb),
	.rx(i_rx_regfcrc_data_wr_tb),
	.y(mux8_out)
	
);


    	// initialize the object with the default values in the class defined as bit >> 0
    	configuration conf_obj ;


    	// inputs to be randomized 

    	//////////////////////// DWORD0  //////////////////////
    	reg [2:0] RAND_CMD_ATTR      ;
    	reg [3:0] RAND_TID           ;
 		reg [7:0] RAND_CMD           ;
 		reg 	  RAND_CP            ;
 		reg [4:0] RAND_DEV_INDEX     ;
 		reg [1:0] RAND_RESERVED      ;
 		reg [2:0] RAND_DTT           ; 	 	 // or {DBP,SRE,reserved}
 		reg [2:0] RAND_MODE          ;
 		reg  	  RAND_RnW           ;
 		reg   	  RAND_WROC          ;
 		reg 	  RAND_TOC           ;

    	//////////////////////// DWORD1  //////////////////////
    	reg [7:0] RAND_DEF_BYTE     ;
    	reg [7:0] RAND_DATA_TWO     ;
    	reg [7:0] RAND_DATA_THREE   ;
    	reg [7:0] RAND_DATA_FOUR    ;

    	/////////////////////// SDA Line //////////////////////
    	//reg  	  RAND_SDA ;

    	integer i ;

	//----------------------------------- Functional Coverage --------------------------------------//
	//------------------------------------ FIRST GROUP ENEC_B -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup ENEC_Broadcast @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			//illegal_bins tx_exit_pattern  = {exit_pattern};

			// sequence bin to be added 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			//illegal_bins tx_restart_pattern  = {restart_pattern};

			// sequence bin to be added 
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 0 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			//illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 1 && i_engine_en_tb)
		{
			//illegal_bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins first_rx_pre = {0};
			bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_Broadcast = {0};
			illegal_bins o_frmcnt_Direct = {1};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location - 1};
			ignore_bins last_addres_of_prev_cmd = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1)
		{
			bins CCC_value = {ENEC_B};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		ENEC_Broadcast  ENEC_Broadcast_instance = new();
		



	//-------------------------------------------- SECOND GROUP DISEC_B---------------------------------------//

	covergroup DISEC_Broadcast @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 ) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 0 && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			//illegal_bins tx_exit_pattern  = {exit_pattern};

			// sequence bin to be added 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 1 && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			//illegal_bins tx_restart_pattern  = {restart_pattern};

		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}
		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 0 && i_engine_en_tb) 
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			//illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb == 1 && i_engine_en_tb) 
		{
			//illegal_bins o_stall_cycles_restart = {restart_pattern_stall};  // as long as broadcast
			bins o_stall_cycles_exit    = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins first_rx_pre = {0};
			bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_Broadcast  = {0};
			illegal_bins o_frmcnt_Direct = {1};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location-1};
			ignore_bins last_addres_of_prev_cmd = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins CCC_value = {DISEC_B};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h01 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h00 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	DISEC_Broadcast  DISEC_Broadcast_instance = new();




	//------------------------------------ Third GROUP SETMWL_B -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup SETMWL_Broadcast @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};

		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			illegal_bins tx_restart_pattern  = {restart_pattern};

		}

		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb == 0 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb == 1 && i_engine_en_tb)
		{
			illegal_bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins first_rx_pre = {0};
			bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_Broadcast = {0};
			illegal_bins o_frmcnt_Direct = {1};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location  = {first_location + 4};
			bins o_regf_addr_second_location = {first_location + 5};
			bins o_regf_addr_zeros = {first_location - 1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2)
		{
			bins CCC_value = {SETMWL_B};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h09 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		SETMWL_Broadcast  SETMWL_Broadcast_instance = new();
		


	//------------------------------------ fourth GROUP SETMWL_B -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup SETMRL_Broadcast @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};

		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			illegal_bins tx_restart_pattern  = {restart_pattern};

		}

		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb == 0 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb == 1 && i_engine_en_tb)
		{
			illegal_bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins first_rx_pre = {0};
			bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_Broadcast = {0};
			illegal_bins o_frmcnt_Direct = {1};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location  = {first_location + 4};
			bins o_regf_addr_second_location = {first_location + 5};
			bins o_regf_addr_zeros = {first_location - 1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2)
		{
			bins CCC_value = {SETMRL_B};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h0A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		SETMRL_Broadcast  SETMRL_Broadcast_instance = new();
		


	//------------------------------------ fifth GROUP Dummy_B -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup Dummy_Broadcast @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			//illegal_bins tx_exit_pattern  = {exit_pattern};

			// sequence bin to be added 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			//illegal_bins tx_restart_pattern  = {restart_pattern};

			// sequence bin to be added 
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && i_regf_TOC_tb == 0 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			//illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && i_regf_TOC_tb == 1 && i_engine_en_tb)
		{
			//illegal_bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins first_rx_pre = {0};
			illegal_bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_frmcnt_Broadcast = {0};
			illegal_bins o_frmcnt_Direct = {1};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && i_engine_en_tb) 
		{
			bins o_regf_addr_zeros = {first_location - 1};
			ignore_bins last_addres_of_prev_cmd = {first_location + 5 ,first_location + 4} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0 && i_engine_en_tb)
		{
			bins CCC_value = {Dummy_B};
			illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h1F && i_regf_DTT_tb == 3'd0) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		Dummy_Broadcast  Dummy_Broadcast_instance = new();













































/////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////// DIRECT ///////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////

//------------------------------------ fifth GROUP ENEC_D -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup ENEC_Direct @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern}; 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 && !i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_internal_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
			//ignore_bins other_modes_rx = {default} ;
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins first_rx_pre = {0};
			//bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_Broadcast = {1};
			illegal_bins o_frmcnt_Direct = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location - 1};
			ignore_bins last_addres_of_prev_cmd = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1)
		{
			bins CCC_value = {ENEC_D};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h80 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		ENEC_Direct  ENENEC_Direct_instance = new();
		


//------------------------------------ sixth GROUP DISEC_D -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup DISEC_Direct @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 )
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern}; 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 && !i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_internal_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
			//ignore_bins other_modes_rx = {default} ;
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins first_rx_pre = {0};
			//bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_frmcnt_Direct = {1};
			illegal_bins o_frmcnt_Broadcast = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location - 1};
			ignore_bins last_addres_of_prev_cmd = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1)
		{
			bins CCC_value = {DISEC_D};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h81 && i_regf_DTT_tb == 3'd1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		DISEC_Direct  DISEC_Direct_instance = new();
		






//------------------------------------ seventh GROUP SETMWL_D  -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup SETMWL_Direct @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2)
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern}; 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_internal_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
			//ignore_bins other_modes_rx = {default} ;
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins first_rx_pre  = {0};
			//bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_Direct = {1};
			illegal_bins o_frmcnt_Broadcast = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location - 1};
			bins o_regf_addr_second_location = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2)
		{
			bins CCC_value = {SETMWL_D};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h89 && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		SETMWL_Direct  SETMWL_Direct_instance = new();
		


//------------------------------------ eighth GROUP SETMRL_D  -----------------------------------------//
	// for every two rows in the excell sheet corresponds to a covergroup

	covergroup SETMRL_Direct @(posedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb 
		iff (i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2)
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern}; 
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2 && !i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2 && i_regf_TOC_tb && i_engine_en_tb)
		{
			bins o_stall_cycles_internal_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}


		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins rx_preamble_rx_mode = {preamble_rx_mode};
			//ignore_bins other_modes_rx = {default} ;
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins first_rx_pre  = {0};
			//bins second_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_frmcnt_Direct = {1};
			illegal_bins o_frmcnt_Broadcast = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_wr_en_n = {0};
			illegal_bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2 && i_engine_en_tb) 
		{
			bins o_regf_addr_first_location = {first_location + 4};
			bins o_regf_addr_zeros = {first_location - 1};
			bins o_regf_addr_second_location = {first_location + 5} ;
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2)
		{
			bins CCC_value = {SETMRL_D};
			//ignore_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			bins others = default ;
		}

		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd1 && i_regf_CMD_tb == 8'h8A && i_regf_DTT_tb == 3'd2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup


		SETMRL_Direct  SETMRL_Direct_instance = new();





































//////////////////////////////////////////////////////// DIRECT GET /////////////////////////////////////////////////

	//----------------------------------------------- ninth GROUP GETMWL_D ----------------------------------------//

	covergroup GETMWL_Direct @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 2) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins first_word_rx_pre = {0};
			illegal_bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_addr_first_location = {first_location + 8};
			bins o_regf_addr_second_location = {first_location + 9};
			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins CCC_value = {GETMWL_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8B && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETMWL_Direct  GETMWL_Direct_instance = new();






//----------------------------------------------- tenth GROUP GETMRL_D ----------------------------------------//

	covergroup GETMRL_Direct @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 2) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins first_word_rx_pre = {0};
			illegal_bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_addr_first_location = {first_location + 8};
			bins o_regf_addr_second_location = {first_location + 9};
			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins CCC_value = {GETMRL_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8C && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETMRL_Direct  GETMRL_Direct_instance = new();




	//----------------------------------------------- eleventh GROUP GETSTATUS_D ----------------------------------------//

	covergroup GETSTATUS_Direct @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 2) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2)
		{
			bins first_word_rx_pre = {0};
			illegal_bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_addr_first_location = {first_location + 8};
			bins o_regf_addr_second_location = {first_location + 9};
			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins CCC_value = {GETSTATUS_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h90 && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETSTATUS_Direct  GETSTATUS_Direct_instance = new();


	//----------------------------------------------- twelvth GROUP GETBCR_D ----------------------------------------//

	covergroup GETBCR_Direct @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 1) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins first_word_rx_pre = {0};
			illegal_bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_addr_first_location = {first_location + 8};
			bins o_regf_addr_second_location = {first_location + 9};
			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins CCC_value = {GETBCR_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8E && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETBCR_Direct  GETBCR_Direct_instance = new();




	//----------------------------------------------- thirteenth GROUP GETDCR_D ----------------------------------------//

	covergroup GETDCR_Direct @(negedge i_sys_clk_tb);
		// coverpoint for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 1) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins first_word_rx_pre = {0};
			illegal_bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_regf_addr_first_location  = {first_location + 8 };
			bins o_regf_addr_second_location = {first_location + 9 };

			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins CCC_value = {GETDCR_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_engine_odd_0 = {0};
			bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1)
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8F && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETDCR_Direct  GETDCR_Direct_instance = new();



/*
	//----------------------------------------------- fourteenth GROUP GETPID_D ----------------------------------------//

	covergroup GETPID_Direct @(negedge i_sys_clk_tb);
		// coverpoints for operands 
		o_tx_en : coverpoint o_tx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && i_regf_DBP_tb == 0 && i_regf_DATA_LEN_tb == 6) 
		{
			bins tx_en_0 = {0};
			bins tx_en_1 = {1};
		}

		o_tx_mode_TOC_0 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6 && !i_regf_TOC_tb && i_engine_en_tb) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_restart_pattern		  = {restart_pattern};
			illegal_bins tx_exit_pattern  = {exit_pattern};
		}

		o_tx_mode_TOC_1 : coverpoint o_tx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6 && i_regf_TOC_tb && i_engine_en_tb ) 
		{
			bins tx_special_preamble 	  = {special_preamble};
			bins tx_zero 				  = {zero};
			bins tx_seven_zeros 		  = {seven_zeros};
			bins tx_serializing_address   = {serializing_address};
			bins tx_parity_calc 		  = {parity_calc};
			bins tx_one 	 			  = {one};
			bins tx_serializing_byte_port = {serializing_byte_port};
			bins tx_c_token_CRC 		  = {c_token_CRC};
			bins tx_value_CRC			  = {value_CRC};
			bins tx_exit_pattern		  = {exit_pattern};
			bins tx_restart_pattern       = {restart_pattern};
		}
		o_sclstall_en : coverpoint o_sclstall_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6 && i_engine_en_tb)
		{
			bins o_sclstall_en_0 = {0};
			bins o_sclstall_en_1 = {1};
		}

		o_sclstall_code_TOC_0 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			illegal_bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_sclstall_code_TOC_1 : coverpoint i_stall_cycles iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && i_regf_TOC_tb && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6 && i_engine_en_tb)
		{
			bins o_stall_cycles_restart = {restart_pattern_stall};
			bins o_stall_cycles_exit = {exit_pattern_stall};
		}

		o_rx_en : coverpoint o_rx_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_rx_en_negedge_0 = {0};
			bins o_rx_en_negedge_1 = {1};
		}

		o_rx_mode : coverpoint o_rx_mode_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6)
		{
			bins rx_preamble_rx_mode   = {preamble_rx_mode};
			bins rx_deserializing_byte = {deserializing_byte};
			bins rx_parity_check       = {parity_check};
			bins rx_check_c_token_CRC  = {check_c_token_CRC};
			bins rx_check_value_CRC    = {check_value_CRC};
		}

		i_rx_pre : coverpoint i_rx_pre_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6)
		{
			bins first_word_rx_pre = {0};
			bins second_word_rx_pre = {1};
		}

		o_frmcnt_en : coverpoint o_frmcnt_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6)
		{
			bins o_frmcnt_en_0 = {0};
			bins o_frmcnt_en_1 = {1};
		}

		o_sdahand_pp_od : coverpoint i_sdr_scl_gen_pp_od_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			//bins o_sdahand_pp_od_0 = {0};
			bins o_sdahand_pp_od_1 = {1};
		}

		o_frmcnt_Direct_Broadcast_n : coverpoint o_frmcnt_Direct_Broadcast_n_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins Direct_flag = {1};
			illegal_bins Broadcast_flag = {0};
		}

		o_regf_wr_en : coverpoint o_regf_wr_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_regf_wr_en_n = {0};
			bins o_regf_wr_en = {1};
		}

		o_regf_rd_en : coverpoint o_regf_rd_en_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_regf_rd_en_0 = {0};
			bins o_regf_rd_en_1 = {1};
		}

		o_regf_addr : coverpoint o_regf_addr_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_regf_addr_first_location  = {first_location + 8};
			bins o_regf_addr_second_location = {first_location + 9};
			bins o_regf_addr_third_location  = {first_location + 10};
			bins o_regf_addr_fourth_location = {first_location + 11};
			bins o_regf_addr_fifth_location  = {first_location + 12};
			bins o_regf_addr_sixth_location  = {first_location + 13};
			bins o_regf_addr_zeros = {first_location-1};
			illegal_bins other_addresses = default ;
		}

		o_txrx_addr_ccc : coverpoint o_txrx_addr_ccc_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins CCC_value = {GETPID_D};
			bins target_address = {[9:40]};
			//illegal_bins others = default ;
		}

		o_engine_odd : coverpoint o_engine_odd_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb  && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_engine_odd_0 = {0};
			illegal_bins o_engine_odd_1 = {1};
		}

		o_regf_ERR_STATUS : coverpoint o_regf_ERR_STATUS_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6)
		{
			bins o_regf_ERR_STATUS_tb = {SUCCESS};
			//illegal_bins others = default ;
		}
		o_engine_done : coverpoint o_engine_done_tb iff (
			i_regf_CMD_ATTR_tb  == 3'd0 && i_regf_CMD_tb == 8'h8D && !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 6) 
		{
			bins o_engine_done_0 = {0};
			bins o_engine_done_1 = {1};
		}

	endgroup

	GETPID_Direct  GETPID_Direct_instance = new();
*/
// 4-initial block 
/* IMPORTANT NOTES :
		1- (General) when driving input to the block which is considered as output of other block u must drive it at posedge not at negdge .
		2- (specifically for our system) : to predict the time to set the tx mode done u count like that >>
				(no. of SCL_DDR clk cycle - 1) + 1 sys clk  
*/

	initial begin 
		// time zero .. these are all signal to be driven in the test bench 
		i_sclgen_rst_n_tb 	   = 1'b1 ;
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		i_engine_en_tb         = 1'b0 ;
		
		//i_rst_n_tb        = 1'b0 ; // asserted 
		#(CLK_PERIOD) i_sclgen_rst_n_tb = 1'b0 ;
		#(CLK_PERIOD) i_sclgen_rst_n_tb = 1'b1 ;
		#(5*CLK_PERIOD) ;

		system_reset(); 
		i_engine_configuration_tb = 12'd1000 ;
		
		#(5*CLK_PERIOD);
		

		// initialization of the object 
		conf_obj = new();

		for (i=0 ; i<100000 ; i++) begin

			assert(conf_obj.randomize());  // "lw feh moshkla fel constrains edeny error" deh lazmet el word assert
			

			RAND_CMD_ATTR  = conf_obj.RAND_CMD_ATTR  ;
			RAND_TID       = conf_obj.RAND_TID       ;
			RAND_CMD       = conf_obj.RAND_CMD       ;
			RAND_CP        = conf_obj.RAND_CP        ;
			RAND_DEV_INDEX = conf_obj.RAND_DEV_INDEX ;
			RAND_RESERVED  = conf_obj.RAND_RESERVED  ;
			RAND_DTT       = conf_obj.RAND_DTT       ;
			RAND_MODE      = conf_obj.RAND_MODE      ;
			RAND_RnW       = conf_obj.RAND_RnW       ;
			RAND_WROC      = conf_obj.RAND_WROC      ;
			RAND_TOC       = conf_obj.RAND_TOC       ;

			RAND_DEF_BYTE   = conf_obj.RAND_DEF_BYTE  ;
			RAND_DATA_TWO   = conf_obj.RAND_DATA_TWO  ;
			RAND_DATA_THREE = conf_obj.RAND_DATA_THREE; 
			RAND_DATA_FOUR  = conf_obj.RAND_DATA_FOUR ; 
			
			i_engine_en_tb = 1'b0 ;
			switch_muxes (configuration_mux);
			input_configuration ();
			switch_muxes (Design_mux);
			i_engine_en_tb = 1'b1 ;

			@(posedge o_engine_done_tb);
			$display("this is testcase no. %d",i,$time);
			#(2*CLK_PERIOD) ;
		end	
		$stop ;
	end

	





/*
		// for second preamble and read data 
//////////////////////////////////////////////  Broadcast driver /////////////////////////////////
// backup works 100 % el7amdulelah 
// for second preamble and read data 
int cycle_count ;
		 // Simulation logic to create the desired pattern (Broadcast)
    initial begin	 		
    	for (i=0 ; i<10000 ; i++) begin
    		#(2*CLK_PERIOD); // One clock cycle delay	
    		wait(i_engine_en_tb);
    		@(negedge scl_neg_edge_tb or  negedge scl_pos_edge_tb)
        		// Step 1: Randomize for 44 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    i_sdahnd_rx_sda_tb = $random();
        		    #(CLK_PERIOD); // One clock cycle delay
        		    cycle_count--;
        		end
        		
        		// Step 2: Hold at zero for 4 cycles
        		i_sdahnd_rx_sda_tb = 0;
        		repeat (7) begin
        		#(CLK_PERIOD); // One clock cycle delay
        		end
        
        		// Step 3: Randomize for 38 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    i_sdahnd_rx_sda_tb =  $random();
        		   	#(CLK_PERIOD); // One clock cycle delay
       		 		cycle_count--;
        		end
        
        		// Step 4: Hold at one for 4 cycles
        		i_sdahnd_rx_sda_tb = 1;
        		repeat (4) begin
        		    #(CLK_PERIOD); // One clock cycle delay
        		end
        		
        		// Step 5: Randomize until engine_done is set to 1
				i_sdahnd_rx_sda_tb = $random();
				#(2*CLK_PERIOD); // One clock cycle delay
				wait (o_engine_done_tb) #(2*CLK_PERIOD);
				continue ;
				  
    	end 
    end
*/

/*

//////////////////////////////////////////////  Direct set driver /////////////////////////////////

	initial begin 
		forever #(2*CLK_PERIOD) begin  
			@(negedge scl_neg_edge_tb or  negedge scl_pos_edge_tb) i_sdahnd_rx_sda_tb = 0 ;
		end
	end 

*/


 /*
//////////////////////////////////////////////  Direct Get driver /////////////////////////////////
// backup works 100 % el7amdulelah 
// for second preamble and read data 
int cycle_count ;
		 // Simulation logic to create the desired pattern (Broadcast)
    initial begin	 		
    	for (i=0 ; i<10000 ; i++) begin
    		#(2*CLK_PERIOD); // One clock cycle delay	
    		wait(i_engine_en_tb);
    		@(negedge scl_neg_edge_tb or  negedge scl_pos_edge_tb)
        		// Step 1: Randomize for 44 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    i_sdahnd_rx_sda_tb = $random();
        		    #(CLK_PERIOD); // One clock cycle delay
        		    cycle_count--;
        		end
        		
        		// Step 2: Hold at zero for 4 cycles
        		i_sdahnd_rx_sda_tb = 0;
        		repeat (12) begin
        		#(CLK_PERIOD); // One clock cycle delay
        		end
        		i_sdahnd_rx_sda_tb = 0;
        		//wait (i_sclstall_stall_done_tb) ;
        		@(negedge o_crc_en_tb) ;
        		#(3*CLK_PERIOD) ;

        		//CRC Preamble 
        		i_sdahnd_rx_sda_tb = 1;
        		#(2*CLK_PERIOD) ;
        		i_sdahnd_rx_sda_tb = 0;
        		#(2*CLK_PERIOD) ;

        		// C token 1100
        		i_sdahnd_rx_sda_tb = 1;
        		#(4*CLK_PERIOD) ;
        		i_sdahnd_rx_sda_tb = 0;
        		#(4*CLK_PERIOD) ;

				wait (o_engine_done_tb) #(2*CLK_PERIOD);
				continue ;
				  
    	end 
    end
*/



//////////////////////////////////////////////  General driver /////////////////////////////////

	initial begin 
		forever #(2*CLK_PERIOD) begin  
			@(negedge scl_neg_edge_tb or negedge scl_pos_edge_tb) i_sdahnd_rx_sda_tb = $random() ;
		end
	end 




///////////////////////////////////////////////////// TASKS ///////////////////////////////////////
	task system_reset ;
		begin 
			@(negedge i_sys_clk_tb)
			i_rst_n_tb = 1'b0 ;
			#(CLK_PERIOD) i_rst_n_tb = 1'b1 ;
		end 
	endtask

	task switch_muxes(input selector);
		begin 
			my_regf_wr_en_tb_selector    = selector ;
			my_regf_data_wr_tb_selector  = selector ;
			my_regf_addr_tb_selector     = selector ;
		end 
	endtask 

	task input_configuration ();
		begin 
			// Randmoized DWORD 0
			@(negedge i_sys_clk_tb) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = { RAND_CMD[0] , RAND_TID , RAND_CMD_ATTR } ;
			my_regf_addr_tb    = config_location ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = { RAND_CP , RAND_CMD[7:1] } ;
			my_regf_addr_tb    = config_location + 1 ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = { RAND_DTT[0] , RAND_RESERVED , RAND_DEV_INDEX } ;
			my_regf_addr_tb    = config_location + 2 ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = { RAND_TOC , RAND_WROC , RAND_RnW , RAND_MODE , RAND_DTT[2:1]} ;
			my_regf_addr_tb    = config_location + 3 ;




			// Randmoized DWORD 1
			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = RAND_DEF_BYTE  ;
			my_regf_addr_tb    = config_location + 4 ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = RAND_DATA_TWO ;
			my_regf_addr_tb    = config_location + 5 ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = RAND_DATA_THREE ;
			my_regf_addr_tb    = config_location + 6 ;

			#(CLK_PERIOD) ;
			my_regf_wr_en_tb   = 1'b1 ;
			my_regf_data_wr_tb = RAND_DATA_FOUR ;
			my_regf_addr_tb    = config_location + 7 ;


			#(CLK_PERIOD) ;

		end 
	endtask 

	 //----------------------------------------------- ASSERTIONS -----------------------------------------------//
	 // Broadcast assertions
	 parameter [1:0] scl_wrt_sys_clk = 2 ;

    // First CMD word
	// Sequence for special preamble
    sequence special_preamble_seq;
        o_tx_mode_tb == special_preamble;
    endsequence


    sequence zero_after_delay;
        special_preamble_seq ##(2*scl_wrt_sys_clk) o_tx_mode_tb == zero;
    endsequence

    
    sequence seven_zeros_seq;
        zero_after_delay ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    
    sequence serializing_byte_port_1_seq;
        seven_zeros_seq ##(7*scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    // Sequence for parity_calc after 8 * scl_period
    sequence parity_calc_seq;
        serializing_byte_port_1_seq ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence

    
    // CCC + DEF DATA WORD
    sequence pre_one_sec ;
        parity_calc_seq ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_1_sec ;
        pre_one_sec ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_port_2_seq ;
        pre_two_1_sec ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_port ;
    endsequence

    sequence serializing_byte_regf_seq ;
        serializing_byte_port_2_seq ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_2_seq ;
        serializing_byte_regf_seq ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence


    // DATA Word 
     sequence pre_one_2_sec ;
        parity_calc_2_seq ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_2_sec ;
        pre_one_2_sec ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_regf_2_seq ;
        pre_two_2_sec ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence serializing_byte_regf_3_seq ;
        serializing_byte_regf_2_seq ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_3_seq ;
        serializing_byte_regf_3_seq ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence


    // crc data word 
    sequence special_preamble_2_sec ;
        parity_calc_3_seq ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble;
    endsequence

    sequence c_token_CRC_seq ;
        special_preamble_2_sec ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq ;
        c_token_CRC_seq ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence







    ////////////////////////////////////////////////// ENDING SEQUENCE ////////////////////////////////////////////////////

    	///////////////////////////////////////////// BROADCAST  //////////////////////////////////////////////////////////
    	// for TOC = 0
    	sequence restart_pattern_seq ;
    	    value_CRC_seq ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    	endsequence
    	sequence broadcast_sec_TOC_0 ;
    	    restart_pattern_seq ##(13) o_tx_mode_tb == special_preamble  ;
    	endsequence


    	// for TOC = 1 
		sequence exit_pattern_seq ;
    	    value_CRC_seq ##(5*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern ;
    	endsequence
    	sequence broadcast_sec_TOC_1 ;
    	    exit_pattern_seq ##(18) o_tx_mode_tb == special_preamble  ;
    	endsequence




    	//////////////////////////////////////////////////// Dummy assertions /////////////////////////////////////
    	// First CMD word
	// Sequence for special preamble
    sequence special_preamble_seq_dummy;
        o_tx_mode_tb == special_preamble;
    endsequence

    sequence zero_after_delay_dummy;
        special_preamble_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == zero;
    endsequence

    sequence seven_zeros_seq_dummy;
        zero_after_delay_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    sequence serializing_byte_port_1_seq_dummy;
        seven_zeros_seq_dummy ##(7*scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    sequence parity_calc_seq_dummy;
        serializing_byte_port_1_seq_dummy ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence

    

    // CCC + DEF DATA WORD
    sequence pre_one_sec_dummy ;
        parity_calc_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_1_sec_dummy ;
        pre_one_sec_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_port_2_seq_dummy ;
        pre_two_1_sec_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_port ;
    endsequence

    sequence serializing_byte_regf_seq_dummy ;
        serializing_byte_port_2_seq_dummy ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_2_seq_dummy ;
        serializing_byte_regf_seq_dummy ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence



    // crc data word 
    sequence special_preamble_2_sec_dummy ;
        parity_calc_2_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble;
    endsequence

    sequence c_token_CRC_seq_dummy ;
        special_preamble_2_sec_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq_dummy ;
        c_token_CRC_seq_dummy ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence

		
		// for TOC = 0
    	sequence restart_pattern_seq_dummy ;
    	    value_CRC_seq_dummy ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    	endsequence
    	sequence Dummy_sec_TOC_0 ;
    	    restart_pattern_seq_dummy ##(13) o_tx_mode_tb == special_preamble  ;
    	endsequence


    	// for TOC = 1 
		sequence exit_pattern_seq_dummy ;
    	    value_CRC_seq_dummy ##(5*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern ;
    	endsequence
    	sequence Dummy_sec_TOC_1 ;
    	    exit_pattern_seq_dummy ##(18) o_tx_mode_tb == special_preamble  ;
    	endsequence



    // Property to combine all sequences
    // ENEC & DISEC 
    property Broadcast_ENEC_DISEC_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 ) && 
        											i_regf_DTT_tb == 3'd1             && 
        											i_regf_TOC_tb == 0 		    	       ) |-> broadcast_sec_TOC_0 ;
    endproperty


  	property Broadcast_ENEC_DISEC_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 ) && 
        											i_regf_DTT_tb == 3'd1             && 
        											i_regf_TOC_tb == 1 		    	       ) |-> broadcast_sec_TOC_1 ;
    endproperty



    // SETMWL & SETMRL 
   	property Broadcast_SETMWL_SETMRL_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A ) && 
        											i_regf_DTT_tb == 3'd2             && 
        											i_regf_TOC_tb == 0 		    	       ) |-> broadcast_sec_TOC_0 ;
    endproperty


  	property Broadcast_SETMWL_SETMRL_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A ) && 
        											i_regf_DTT_tb == 3'd2             && 
        											i_regf_TOC_tb == 1 		    	       ) |-> broadcast_sec_TOC_1 ;
    endproperty



    // Dummy CCC 0x1F 
   	property Broadcast_Dummy_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  					(i_regf_CMD_tb == 8'h1F) 		  && 
        											i_regf_DTT_tb == 3'd0             && 
        											i_regf_TOC_tb == 0 		    	       ) |-> Dummy_sec_TOC_0 ;
    endproperty


  	property Broadcast_Dummy_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  					(i_regf_CMD_tb == 8'h1F) 		  && 
        											i_regf_DTT_tb == 3'd0             && 
        											i_regf_TOC_tb == 1 		    	       ) |-> Dummy_sec_TOC_1 ;
    endproperty







    /////////////////// tracking assertions ///////////////////////

	property Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        	(i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 || i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A) && 
        						  (i_regf_DTT_tb == 3'd1 || i_regf_DTT_tb == 3'd2)    && 
        											i_regf_TOC_tb == 0 ) 
        											|->  
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == serializing_byte_regf 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])
    
        			;										 
    endproperty

    

    property Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        	(i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 || i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A) && 
        						  (i_regf_DTT_tb == 3'd1 || i_regf_DTT_tb == 3'd2)    && 
        											i_regf_TOC_tb == 1 ) 
        											|->  
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == serializing_byte_regf 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == exit_pattern 		    [*(18)])
    
        			;										 
    endproperty

   

    property Broadcast_Dummy_TOC_0_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        											(i_regf_CMD_tb == 8'h1F)          && 
        											i_regf_DTT_tb == 3'd0             && 
        											i_regf_TOC_tb == 0 ) 
        											|->  
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])
    
        			;										 
    endproperty


    property Broadcast_Dummy_TOC_1_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        											(i_regf_CMD_tb == 8'h1F)          && 
        											i_regf_DTT_tb == 3'd0             && 
        											i_regf_TOC_tb == 1 ) 
        											|->  
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == exit_pattern 		    [*(18)])
    
        			;										 
    endproperty



    // Asserting Broadcast properites 
    assert property(Broadcast_ENEC_DISEC_TOC_0)
                            $display("%t Broadcast_ENEC_DISEC_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_TOC_0 FAILED ",$time);
   
    assert property(Broadcast_ENEC_DISEC_TOC_1)
                            $display("%t Broadcast_ENEC_DISEC_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_TOC_1 FAILED ",$time);
 
    assert property(Broadcast_SETMWL_SETMRL_TOC_0)
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_0 FAILED ",$time);
  
    assert property(Broadcast_SETMWL_SETMRL_TOC_1)
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_1 FAILED ",$time);
 
    assert property(Broadcast_Dummy_TOC_0)
                            $display("%t Broadcast_Dummy_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_0 FAILED ",$time);
    
    assert property(Broadcast_Dummy_TOC_1)
                            $display("%t Broadcast_Dummy_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_1 FAILED ",$time);                     

    assert property(Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track)
                            $display("%t Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track FAILED ",$time);	

    assert property(Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track)
                            $display("%t Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track FAILED ",$time);	

    assert property(Broadcast_Dummy_TOC_0_track)
                            $display("%t Broadcast_Dummy_TOC_0_track PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_0_track FAILED ",$time);	

    assert property(Broadcast_Dummy_TOC_1_track)
                            $display("%t Broadcast_Dummy_TOC_1_track PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_1_track FAILED ",$time);



/////////////////////////////////////////////////// DIRECT CCC's ///////////////////////////////////////////////////////////
	
	
    ///////////////////////////////////////////// Direct secuence  //////////////////////////////////////////////////////////
    	
    // First CMD word
	// Sequence for special preamble
    sequence special_preamble_seq_1_D ;
        o_tx_mode_tb == special_preamble;
    endsequence


    sequence zero_after_delay_1_D;
        special_preamble_seq_1_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == zero;
    endsequence

    
    sequence seven_zeros_seq_1_D;
        zero_after_delay_1_D ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    
    sequence serializing_byte_port_1_seq_1_D;
        seven_zeros_seq_1_D ##(7 * scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    // Sequence for parity_calc after 8 * scl_period
    sequence parity_calc_seq_1_D;
        serializing_byte_port_1_seq_1_D ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence

    
    // CCC + DEF DATA WORD
    sequence pre_one_sec_1_D ;
        parity_calc_seq_1_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_1_sec_1_D ;
        pre_one_sec_1_D ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_port_2_seq_1_D ;
        pre_two_1_sec_1_D ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_port ;
    endsequence

    sequence serializing_byte_regf_seq_1_D ;
        serializing_byte_port_2_seq_1_D ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_2_seq_1_D ;
        serializing_byte_regf_seq_1_D ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence


    // CRC data word 
    sequence special_preamble_2_sec_1_D ;
        parity_calc_2_seq_1_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble;
    endsequence

    sequence c_token_CRC_seq_1_D ;
        special_preamble_2_sec_1_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq_1_D ;
        c_token_CRC_seq_1_D ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence


    // First Restart Pattern
    sequence restart_pattern_seq_1_D ;
    	value_CRC_seq_1_D ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    endsequence

    sequence broadcast_sec_TOC_0_1_D ;
    	restart_pattern_seq_1_D ##(13) o_tx_mode_tb == special_preamble  ;
    endsequence


    // Second CMD word
    sequence zero_after_delay_2_D;
        broadcast_sec_TOC_0_1_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == zero;
    endsequence

    
    sequence seven_zeros_seq_2_D;
        zero_after_delay_2_D ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    
    sequence serializing_byte_port_1_seq_2_D;
        seven_zeros_seq_2_D ##(7 * scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    // Sequence for parity_calc after 8 * scl_period
    sequence parity_calc_3_seq_2_D;
        serializing_byte_port_1_seq_2_D ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence



    // DATA Word 
    sequence pre_one_2_sec_2_D ;
        parity_calc_3_seq_2_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one ;
    endsequence

    sequence pre_two_2_sec_2_D ;
        pre_one_2_sec_2_D ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_regf_2_seq_2_D ;
        pre_two_2_sec_2_D ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence serializing_byte_regf_3_seq_2_D ;
        serializing_byte_regf_2_seq_2_D ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_4_seq_2_D ;
        serializing_byte_regf_3_seq_2_D ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence


    // second CRC data word 
    sequence special_preamble_2_sec_2_D ;
        parity_calc_4_seq_2_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble;
    endsequence

    sequence c_token_CRC_seq_2_D ;
        special_preamble_2_sec_2_D ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq_2_D ;
        c_token_CRC_seq_2_D ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence



    	// for TOC = 0
    	sequence restart_pattern_seq_2_D ;
    	    value_CRC_seq_2_D ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    	endsequence
    	sequence Direct_sec_TOC_0 ;
    	    restart_pattern_seq_2_D ##(13) o_tx_mode_tb == special_preamble  ;
    	endsequence


    	// for TOC = 1 
		sequence exit_pattern_seq_D ;
    	    value_CRC_seq_2_D ##(5*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern ;
    	endsequence
    	sequence Direct_sec_TOC_1 ;
    	    exit_pattern_seq_D ##(18) o_tx_mode_tb == special_preamble  ;
    	endsequence




	// ENEC & DISEC
	property Direct_ENEC_DISEC_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h80 || i_regf_CMD_tb == 8'h81 ) && 
        											i_regf_DTT_tb == 3'd1             && 
        						   i_regf_TOC_tb == 0 && !i_regf_RnW_tb 		    	   ) |-> Direct_sec_TOC_0 ;
    endproperty

    property Direct_ENEC_DISEC_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h80 || i_regf_CMD_tb == 8'h81 ) && 
        											i_regf_DTT_tb == 3'd1             && 
        						   i_regf_TOC_tb == 1 && !i_regf_RnW_tb		    	       ) |-> Direct_sec_TOC_1 ;
    endproperty


    // SETMWL & SETMRL
	property Direct_SETMWL_SETMRL_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h89 || i_regf_CMD_tb == 8'h8A ) && 
        											i_regf_DTT_tb == 3'd2             && 
        						   i_regf_TOC_tb == 0 && !i_regf_RnW_tb		    	       ) |-> Direct_sec_TOC_0 ;
    endproperty

    property Direct_SETMWL_SETMRL_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        						  (i_regf_CMD_tb == 8'h89 || i_regf_CMD_tb == 8'h8A ) && 
        											i_regf_DTT_tb == 3'd2             && 
        						  i_regf_TOC_tb == 1 	&& !i_regf_RnW_tb	    	       ) |-> Direct_sec_TOC_1 ;
    endproperty


    property Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        	(i_regf_CMD_tb == 8'h80 || i_regf_CMD_tb == 8'h81 || i_regf_CMD_tb == 8'h89 || i_regf_CMD_tb == 8'h8A) && 
        							(i_regf_DTT_tb == 3'd1 || i_regf_DTT_tb == 3'd1 ) && 
        											i_regf_TOC_tb == 0 ) 
        											|->  
        // CMD word											
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])				 ##1
     	// CMD word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == serializing_byte_regf 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])
    
        			;										 
    endproperty

    property Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd1       && 
        	(i_regf_CMD_tb == 8'h80 || i_regf_CMD_tb == 8'h81 || i_regf_CMD_tb == 8'h89 || i_regf_CMD_tb == 8'h8A) && 
        							(i_regf_DTT_tb == 3'd1 || i_regf_DTT_tb == 3'd1 ) && 
        											i_regf_TOC_tb == 1 ) 
        											|->  
        // CMD word											
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])				 ##1
     	// CMD word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == serializing_byte_regf 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == exit_pattern   		[*(18)])
    
        			;										 
    endproperty




     // Asserting the properties
    assert property(Direct_ENEC_DISEC_TOC_0)
                            $display("%t Direct_ENEC_DISEC_TOC_0 PASSED ",$time); else
                            $display("%t Direct_ENEC_DISEC_TOC_0 FAILED ",$time);

   
    assert property(Direct_ENEC_DISEC_TOC_1)
                            $display("%t Direct_ENEC_DISEC_TOC_1 PASSED ",$time); else
                            $display("%t Direct_ENEC_DISEC_TOC_1 FAILED ",$time);

    
    assert property(Direct_SETMWL_SETMRL_TOC_0)
                            $display("%t Direct_SETMWL_SETMRL_TOC_0 PASSED ",$time); else
                            $display("%t Direct_SETMWL_SETMRL_TOC_0 FAILED ",$time);

   
    assert property(Direct_SETMWL_SETMRL_TOC_1)
                            $display("%t Direct_SETMWL_SETMRL_TOC_1 PASSED ",$time); else
                            $display("%t Direct_SETMWL_SETMRL_TOC_1 FAILED ",$time);

    assert property(Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track)
                            $display("%t Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track PASSED ",$time); else
                            $display("%t Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_0_track FAILED ",$time);

    assert property(Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track)
                            $display("%t Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track PASSED ",$time); else
                            $display("%t Direct_ENEC_DISEC_SETMWL_SETMRL_TOC_1_track FAILED ",$time);                       

/////////////////////////////////////////////////////////// DIRECT GET /////////////////////////////////////////////////////////
    	
    // First CMD word
	// Sequence for special preamble
    sequence special_preamble_seq_1_D_get ;
        o_tx_mode_tb == special_preamble;
    endsequence

    sequence zero_after_delay_1_D_get;
        special_preamble_seq_1_D_get ##(2 * scl_wrt_sys_clk) o_tx_mode_tb == zero;  // still zero even it it was a Direct get CCC
    endsequence
    
    sequence seven_zeros_seq_1_D_get;
        zero_after_delay_1_D_get ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    sequence serializing_byte_port_1_seq_1_D_get;
        seven_zeros_seq_1_D_get ##(7 * scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    // Sequence for parity_calc after 8 * scl_period
    sequence parity_calc_seq_1_D_get;
        serializing_byte_port_1_seq_1_D_get ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence

    
    // CCC + DEF DATA WORD
    sequence pre_one_sec_1_D_get ;
        parity_calc_seq_1_D_get ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_1_sec_1_D_get ;
        pre_one_sec_1_D_get ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_port_2_seq_1_D_get ;
        pre_two_1_sec_1_D_get ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_port ;
    endsequence

    sequence serializing_byte_regf_seq_1_D_get ;
        serializing_byte_port_2_seq_1_D_get ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_2_seq_1_D_get ;
        serializing_byte_regf_seq_1_D_get ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence


    // CRC data word 
    sequence special_preamble_2_sec_1_D_get ;
        parity_calc_2_seq_1_D_get ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence c_token_CRC_seq_1_D_get ;
        special_preamble_2_sec_1_D_get ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq_1_D_get ;
        c_token_CRC_seq_1_D_get ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence


    // First Restart Pattern
    sequence restart_pattern_seq_1_D_get ;
    	value_CRC_seq_1_D_get ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    endsequence

    sequence broadcast_sec_TOC_0_1_D_get ;
    	restart_pattern_seq_1_D_get ##(13) o_tx_mode_tb == special_preamble  ;
    endsequence


    // Second CMD word
    sequence zero_after_delay_2_D_get;
        broadcast_sec_TOC_0_1_D_get ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one ;        // READ OPERATION YA 7MAAAR
    endsequence

    
    sequence seven_zeros_seq_2_D_get ;
        zero_after_delay_2_D_get ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros ;
    endsequence

    
    sequence serializing_byte_port_1_seq_2_D_get ;
        seven_zeros_seq_2_D_get ##(7 * scl_wrt_sys_clk) o_tx_mode_tb == serializing_address ;
    endsequence

    sequence parity_calc_3_seq_2_D_get ;
        serializing_byte_port_1_seq_2_D_get ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence



    // DATA Word 
    sequence pre_one_2_sec_2_D_get ;
        parity_calc_3_seq_2_D_get ##(2 * scl_wrt_sys_clk) o_tx_mode_tb == one ;
    endsequence

    sequence pre_two_2_sec_2_D_get ;
        pre_one_2_sec_2_D_get ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ; // i.e Disabled
    endsequence


    	// for TOC = 0
    	sequence restart_pattern_seq_2_D_get ;
    	    pre_two_2_sec_2_D_get ##(30*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
    	endsequence
    	// for TOC = 0
    	sequence Direct_get_2_bytes_sec_TOC_0 ;
    	    restart_pattern_seq_2_D_get ##(11) (o_tx_mode_tb == special_preamble)  ;
    	endsequence



    	// for TOC = 1
    	sequence exit_pattern_seq_2_D_get ;
    	    pre_two_2_sec_2_D_get ##(30*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern  ;
    	endsequence
    	// for TOC = 1 
		sequence Direct_get_2_bytes_sec_TOC_1 ;
    	    exit_pattern_seq_2_D_get ##(17) (o_tx_mode_tb == special_preamble) ;
    	endsequence



// direct get 

	// GETMWL & GETMRL & GETSTATUS
	property Direct_GETMWL_GETMRL_GETSTATUS_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C)  && 
        					    !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2             && 
        						   i_regf_TOC_tb == 0 && i_regf_RnW_tb		    	       ) |-> Direct_get_2_bytes_sec_TOC_0 ;
    endproperty

    property Direct_GETMWL_GETMRL_GETSTATUS_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C)  && 
        						!i_regf_DBP_tb && i_regf_DATA_LEN_tb == 2             && 
        						  i_regf_TOC_tb == 1 && i_regf_RnW_tb	    	           ) |-> Direct_get_2_bytes_sec_TOC_1 ;
    endproperty


 	// Assert the property
    assert property(Direct_GETMWL_GETMRL_GETSTATUS_TOC_0)
                            $display("%t Direct_GETMWL_GETMRL_GETSTATUS_TOC_0 PASSED ",$time); else
                            $display("%t Direct_GETMWL_GETMRL_GETSTATUS_TOC_0 FAILED ",$time);

    // Assert the property
    assert property(Direct_GETMWL_GETMRL_GETSTATUS_TOC_1)
                            $display("%t Direct_GETMWL_GETMRL_GETSTATUS_TOC_1 PASSED ",$time); else
                            $display("%t Direct_GETMWL_GETMRL_GETSTATUS_TOC_1 FAILED ",$time);





    // GETBCR & GETDCR 
	property Direct_GETBCR_GETDCR_TOC_0 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        						  (i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        					    !i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1             && 
        						   i_regf_TOC_tb == 0 && i_regf_RnW_tb		    	       ) |-> Direct_get_2_bytes_sec_TOC_0 ;
    endproperty

    property Direct_GETBCR_GETDCR_TOC_1 ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        						  (i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        						!i_regf_DBP_tb && i_regf_DATA_LEN_tb == 1             && 
        						  i_regf_TOC_tb == 1 && i_regf_RnW_tb	    	           ) |-> Direct_get_2_bytes_sec_TOC_1 ;
    endproperty



    // Assert the property
    assert property(Direct_GETBCR_GETDCR_TOC_0)
                            $display("%t Direct_GETBCR_GETDCR_TOC_0 PASSED ",$time); else
                            $display("%t Direct_GETBCR_GETDCR_TOC_0 FAILED ",$time);

    // Assert the property
    assert property(Direct_GETBCR_GETDCR_TOC_1)
                            $display("%t Direct_GETBCR_GETDCR_TOC_1 PASSED ",$time); else
                            $display("%t Direct_GETBCR_GETDCR_TOC_1 FAILED ",$time);



    ////////////////////////// tracking assertions 
    property Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C || i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        						!i_regf_DBP_tb && (i_regf_DATA_LEN_tb == 2 || i_regf_DATA_LEN_tb == 1)          && 
        						 i_regf_TOC_tb == 0 && i_regf_RnW_tb	    	           ) 
        											|->  
        // CMD word											
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])				 ##1
     	// CMD word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1  	// RnW bit = 1 
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one  			 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 	    [*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == special_preamble 		[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])
    
        			;										 
    endproperty

    // Assert the property
    assert property(Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_track)
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_track PASSED ",$time); else
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_track FAILED ",$time);


    ////////////////////////// tracking assertions 
     property Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C || i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        						!i_regf_DBP_tb && (i_regf_DATA_LEN_tb == 2 || i_regf_DATA_LEN_tb == 1)          && 
        						 i_regf_TOC_tb == 1 && i_regf_RnW_tb	    	           ) 
        											|->  
        // CMD word											
        (o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_tx_mode_tb == zero 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == serializing_byte_port  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_byte_regf  [*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == c_token_CRC 			[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == value_CRC 				[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == restart_pattern 		[*(12)])				 ##1
     	// CMD word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == one 					[*(scl_wrt_sys_clk)])    ##1  	// RnW bit = 1 
     	(o_tx_mode_tb == seven_zeros 			[*(7*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == serializing_address 	[*(8*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == parity_calc 			[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_tx_mode_tb == one  			 		[*(scl_wrt_sys_clk)])    ##1
     	(o_tx_mode_tb == special_preamble 	    [*(scl_wrt_sys_clk)])    ##1     // disabled 
     	(o_tx_mode_tb == special_preamble 		[*(16*scl_wrt_sys_clk)]) ##1
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_tx_mode_tb == special_preamble 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == special_preamble 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_tx_mode_tb == exit_pattern 	 		[*(18)])
    
        			;										 
    endproperty

    // Assert the property
    assert property(Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_track)
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_track PASSED ",$time); else
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_track FAILED ",$time);



    property Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_rx_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C || i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        						!i_regf_DBP_tb && (i_regf_DATA_LEN_tb == 2 || i_regf_DATA_LEN_tb == 1)          && 
        						 i_regf_TOC_tb == 0 && i_regf_RnW_tb	    	           ) 
        											|->  
        // CMD word											
        (o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_rx_mode_tb == preamble_rx_mode 		[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode  		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode  		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(12)])				 ##1
     	// CMD word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1  	// RnW bit = 1 
     	(o_rx_mode_tb == preamble_rx_mode 		[*(7*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_rx_mode_tb == preamble_rx_mode  		[*(scl_wrt_sys_clk)])    ##1   // disabled 
     	(o_rx_mode_tb == preamble_rx_mode 	    [*(3)])  				 ##1   // due to transition between tx and rx  
     	(o_rx_mode_tb == deserializing_byte 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_rx_mode_tb == parity_check 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_rx_mode_tb == CRC_PREAMBLE 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == check_c_token_CRC 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == check_value_CRC 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(11)])	 		 	 	 	//  disabled >> restart_pattern
    
        			;										 
    endproperty

    // Assert the property
    assert property(Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_rx_track)
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_rx_track PASSED ",$time); else
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_0_rx_track FAILED ",$time);


    property Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_rx_track ;
        @(posedge i_sys_clk_tb) ($rose(i_engine_en_tb) 								  &&
        											i_regf_CMD_ATTR_tb  == 3'd0       && 
        (i_regf_CMD_tb == 8'h8B || i_regf_CMD_tb == 8'h8C || i_regf_CMD_tb == 8'h90 || i_regf_CMD_tb == 8'h8F || i_regf_CMD_tb == 8'h8E)  && 
        						!i_regf_DBP_tb && (i_regf_DATA_LEN_tb == 2 || i_regf_DATA_LEN_tb == 1)          && 
        						 i_regf_TOC_tb == 1 && i_regf_RnW_tb	    	           ) 
        											|->  
        // CMD word											
        (o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
        (o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(7*scl_wrt_sys_clk)])  ##1     	
     	(o_rx_mode_tb == preamble_rx_mode 		[*(8*scl_wrt_sys_clk)])  ##1     	
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1
     	(o_rx_mode_tb == preamble_rx_mode  		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode  		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(12)])				 ##1
     	// CMD word
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(scl_wrt_sys_clk)])    ##1  	// RnW bit = 1 
     	(o_rx_mode_tb == preamble_rx_mode 		[*(7*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(8*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(2*scl_wrt_sys_clk)])  ##1
     	// DATA word
     	(o_rx_mode_tb == preamble_rx_mode  		[*(scl_wrt_sys_clk)])    ##1   // disabled 
     	(o_rx_mode_tb == preamble_rx_mode 	    [*(3)])  				 ##1   // due to transition between tx and rx  
     	(o_rx_mode_tb == deserializing_byte 	[*(16*scl_wrt_sys_clk)]) ##1
     	(o_rx_mode_tb == parity_check 			[*(2*scl_wrt_sys_clk)])  ##1
     	// CRC word
     	(o_rx_mode_tb == CRC_PREAMBLE 			[*(2*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == check_c_token_CRC 		[*(4*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == check_value_CRC 		[*(5*scl_wrt_sys_clk)])  ##1
     	(o_rx_mode_tb == preamble_rx_mode 		[*(17)])	 		 	 	 	//  disabled >> exit_pattern
    
        			;										 
    endproperty

    // Assert the property
    assert property(Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_rx_track)
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_rx_track PASSED ",$time); else
                            $display("%t Direct_GETDCR_GETBCR_GETSTATUS_GETMWL_GETMRL_TOC_1_rx_track FAILED ",$time);





endmodule 

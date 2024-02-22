module CCC_Handler_tb ();

/*
1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .
*/ 


// 1-signal declaration 
	
	// common signals 
	reg        i_sys_clk_tb = 0 , i_rst_n_tb  ;

	///////////////////////// scl generation ///////////////////////////////
	reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb , o_scl_tb ;

	////////////////////////// bits counter //////////////////////////////// 
	reg  	   i_bitcnt_en_tb ;
	wire [4:0] o_cnt_bit_count_tb ;

	/////////////////////////// CCC Handler /////////////////////////////
	reg        i_engine_en_tb , i_frmcnt_last_frame_tb ,i_sclstall_stall_done_tb  ;
	// related to tx
	reg 	   i_tx_mode_done_tb ,o_tx_en_tb ;
	reg  [3:0] o_tx_mode_tb ;
 	// related to rx
	reg 	   i_rx_mode_done_tb ,i_rx_second_pre_tb ,i_rx_error_tb ,o_rx_en_tb ;
	reg  [2:0] o_rx_mode_tb ;
	// related to regfile (configuration)





	reg  	    i_regf_RnW_tb ,i_regf_TOC_tb , i_regf_WROC_tb , i_regf_DBP_tb , i_regf_SRE_tb ;
	reg  [2:0]  i_regf_CMD_ATTR_tb ;
	reg  [7:0]  i_regf_CMD_tb ;
	reg  [4:0]  i_regf_DEV_INDEX_tb ;
	reg  [2:0]  i_regf_DTT_tb ;
	wire  	    o_regf_wr_en_tb , o_regf_rd_en_tb ;
	wire [15:0] o_regf_addr_tb ; 	 	 	// this may be changed 
	wire  	    o_engine_done_tb ;
	wire [7:0]  o_txrx_addr_ccc_tb ;
	wire   	    o_engine_odd_tb ;

	// related to scl staller 
	wire 	   o_sclstall_en_tb ;
	wire [3:0] o_sclstall_code_tb ;

	//related to frame counter
	wire 	   o_frmcnt_en_tb ;

// 2-clk generation 

	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;


// 3-DUT instatiation 

	CCC_Handler DUT2 (
		.i_sys_clk	            (i_sys_clk_tb),
		.i_sys_rst			    (i_rst_n_tb),
		.i_engine_en 			(i_engine_en_tb),
		.i_bitcnt_number		(o_cnt_bit_count_tb),
		.i_tx_mode_done 		(i_tx_mode_done_tb),
		.i_rx_mode_done 		(i_rx_mode_done_tb),
		.i_rx_second_pre 		(i_rx_second_pre_tb),
		.i_sclstall_stall_done  (i_sclstall_stall_done_tb),
		.i_rx_error 	 	    (i_rx_error_tb),
		.i_frmcnt_last_frame 	(i_frmcnt_last_frame_tb),

		.i_regf_RnW(i_regf_RnW_tb),
		.i_regf_CMD_ATTR(i_regf_CMD_ATTR_tb),
		.i_regf_CMD(i_regf_CMD_tb),
		.i_regf_DEV_INDEX(i_regf_DEV_INDEX_tb),
		.i_regf_TOC(i_regf_TOC_tb),
		.i_regf_WROC(i_regf_WROC_tb),

		.i_regf_DTT(i_regf_DTT_tb),

		.i_regf_DBP(i_regf_DBP_tb),
		.i_regf_SRE(i_regf_SRE_tb),
		//.i_regf_DATA_LENGTH(),

		.o_sclstall_en(o_sclstall_en_tb),
		.o_sclstall_code(o_sclstall_code_tb),
		.o_tx_en(o_tx_en_tb),
		.o_tx_mode(o_tx_mode_tb),
		.o_rx_en(o_rx_en_tb),
		.o_rx_mode(o_rx_mode_tb),
		.o_bitcnt_en(i_bitcnt_en_tb),
		//.o_bitcnt_err_rst(),
		.o_frmcnt_en(o_frmcnt_en_tb),
		.o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb),


		.o_regf_wr_en(o_regf_wr_en_tb),
		.o_regf_rd_en(o_regf_rd_en_tb),
		.o_regf_addr(o_regf_addr_tb),
		.o_engine_done(o_engine_done_tb),
		.o_txrx_addr_ccc(o_txrx_addr_ccc_tb),
		.o_engine_odd(o_engine_odd_tb)

		);


	scl_generation DUT0 (
		.i_sdr_ctrl_clk      (i_sys_clk_tb),
		.i_sdr_ctrl_rst_n 	 (i_rst_n_tb),
		.i_sdr_scl_gen_pp_od (i_sdr_scl_gen_pp_od_tb),
		.i_scl_gen_stall  	 (i_scl_gen_stall_tb),
		.i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb),
		.i_timer_cas         (i_timer_cas_tb),
		.o_scl_pos_edge      (scl_pos_edge_tb),
		.o_scl_neg_edge      (scl_neg_edge_tb),
		.o_scl 	 			 (o_scl_tb)

	);

		bits_counter DUT1 (
		.i_sys_clk       (i_sys_clk_tb),
		.i_rst_n 	     (i_rst_n_tb),
		.i_bitcnt_en     (i_bitcnt_en_tb),
		.i_scl_pos_edge  (scl_pos_edge_tb),
		.i_scl_neg_edge  (scl_neg_edge_tb),
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);

// 4-initial block 
	initial begin 
		// time zero 
		i_rst_n_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		//i_sdr_scl_gen_pp_od_tb = 1'b1 ;
		 
		/////////////////////////////// CCC Handler //////////////////////////////
		i_frmcnt_last_frame_tb = 1'b0 ;
		i_sclstall_stall_done_tb = 1'b0 ;
		i_tx_mode_done_tb = 1'b0 ;
		i_rx_mode_done_tb = 1'b1 ;  // important
		i_rx_second_pre_tb = 1'b0 ;  // important
		i_rx_error_tb = 1'b0 ;

		// configuration 
		i_regf_RnW_tb = 1'b0 ;  	 	// write 
		i_regf_TOC_tb = 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb = 1'b0 ; 	 	// response status is not required 
		i_regf_DBP_tb = 1'b0 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb = 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb = 3'd0 ; 	// 0 regular  , 1 immediate 
		i_regf_CMD_tb = 8'h89 ;	 	 	//  ccc value set max write length (Direct)
		i_regf_DEV_INDEX_tb = 5'd0 ;
		i_regf_DTT_tb = 3'd2 ; 	 	 	// only 2 payload without defining byte 

		i_engine_en_tb = 1'b0 ;


		#(3*CLK_PERIOD);
		i_rst_n_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_rst_n_tb     = 1'b1 ; // not asserted
		// first things first 
		i_engine_en_tb = 1'b1 ;

		i_tx_mode_done_tb = 1'b1 ;

		#(500 * CLK_PERIOD) i_sclstall_stall_done_tb = 1'b1 ;

		#(5000*CLK_PERIOD);
		$stop ;
	end
endmodule 
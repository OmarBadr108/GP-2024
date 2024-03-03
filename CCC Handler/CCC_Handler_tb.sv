module CCC_Handler_tb ();

/*
1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .
*/ 


// 1-signal declaration 
	
	// common signals 
	reg        i_sys_clk_tb = 1 , i_rst_n_tb  ;

	///////////////////////// scl generation ///////////////////////////////
	reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb , o_scl_tb ;

	////////////////////////// bits counter //////////////////////////////// 
	reg  	   i_bitcnt_en_tb ;
	wire [5:0] o_cnt_bit_count_tb ;
	wire  	   o_bitcnt_err_rst_tb ;
	/////////////////////////// CCC Handler /////////////////////////////
	reg        i_engine_en_tb , i_frmcnt_last_frame_tb ,i_sclstall_stall_done_tb  ;
	// related to tx
	reg 	   i_tx_mode_done_tb ,o_tx_en_tb ;
	reg  [3:0] o_tx_mode_tb ;
 	// related to rx
	reg 	   i_rx_mode_done_tb ,i_rx_pre_tb ,i_rx_error_tb ,o_rx_en_tb ;
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
	wire [3:0]  o_regf_ERR_STATUS_tb ;
	// related to scl staller 
	wire 	   o_sclstall_en_tb ;
	wire [3:0] o_sclstall_code_tb ;

	//related to frame counter
	wire 	   o_frmcnt_en_tb ;

// 2-clk generation 

	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;

	// scl ddr clk = 25 Mhz
	parameter DDR_CLK_PERIOD = 40 ;

// 3-DUT instatiation 

	CCC_Handler DUT2 (
		.i_sys_clk	            (i_sys_clk_tb),
		.i_sys_rst			    (i_rst_n_tb),
		.i_engine_en 			(i_engine_en_tb),
		.i_bitcnt_number		(o_cnt_bit_count_tb),
		.i_tx_mode_done 		(i_tx_mode_done_tb),
		.i_rx_mode_done 		(i_rx_mode_done_tb),
		.i_rx_pre 				(i_rx_pre_tb),
		//.i_rx_first_pre 	 	(i_rx_first_pre_tb),
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
		.o_bitcnt_err_rst(o_bitcnt_err_rst_tb),
		.o_frmcnt_en(o_frmcnt_en_tb),
		.o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb),


		.o_regf_wr_en(o_regf_wr_en_tb),
		.o_regf_rd_en(o_regf_rd_en_tb),
		.o_regf_addr(o_regf_addr_tb),
		.o_engine_done(o_engine_done_tb),
		.o_txrx_addr_ccc(o_txrx_addr_ccc_tb),
		.o_engine_odd(o_engine_odd_tb),
		.o_regf_ERR_STATUS(o_regf_ERR_STATUS_tb)
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
		.i_cccnt_err_rst (o_bitcnt_err_rst_tb),
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);
/*
		wire [15:0]	i_regf_DATA_LEN_tb ;
		wire    	i_fcnt_no_frms_tb ;
		wire 	 	i_fcnt_en_tb ;
		wire  	 	o_fcnt_last_frame_tb ;
		


		frame_counter DUT3 (
		.i_fcnt_no_frms (i_fcnt_no_frms_tb),
		.i_fcnt_clk (i_sys_clk_tb),
		.i_fcnt_rst_n (i_rst_n_tb),
		.i_fcnt_en (o_frmcnt_en_tb),
		.i_regf_CMD_ATTR (i_regf_CMD_ATTR_tb),
		.i_regf_DATA_LEN (i_regf_DATA_LEN_tb),
		.i_regf_DTT (i_regf_DTT_tb),
		.i_cnt_bit_count (o_cnt_bit_count_tb),

		.o_fcnt_last_frame (o_fcnt_last_frame_tb),
		.o_cccnt_last_frame (i_frmcnt_last_frame_tb)

	);
*/
// 4-initial block 
/* IMPORTANT NOTES :
		1- (General) when driving input to the block which is considered as output of other block u must drive it at posedge not at negdge .
		2- (specifically for our system) : to predict the time to set the tx mode done u count like that >>
				(no. of SCL_DDR clk cycle - 1) + 1 sys clk  

*/
	initial begin 
		// time zero 
		i_rst_n_tb    		   = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		//i_sdr_scl_gen_pp_od_tb = 1'b1 ;
		 
		/////////////////////////////// CCC Handler //////////////////////////////
		i_frmcnt_last_frame_tb 	 = 1'b0 ;
		i_sclstall_stall_done_tb = 1'b0 ;
		i_tx_mode_done_tb 	 	 = 1'b0 ;
		i_rx_mode_done_tb 	 	 = 1'b0 ;  // important
		i_rx_pre_tb 	 	     = 1'b0 ;  // important
		i_rx_error_tb 	 	     = 1'b0 ;

		// configuration 
		i_regf_RnW_tb 		= 1'b0 ;  	 	// write 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 	// response status is not required 
		i_regf_DBP_tb 		= 1'b0 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 	// 0 regular  , 1 immediate 
		i_regf_DTT_tb 		= 3'd2 ; 	 	 	// only 2 payload without defining byte 

		i_sclstall_stall_done_tb = 1'b0 ;
		i_engine_en_tb 			 = 1'b0 ;


		
		system_reset();

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		


		/* first test case  : braodcast sequence
							  regular 
							  no defining byte 
							  even number of bytes

		*/
		// configuration 
		i_regf_CMD_tb 	 	= 8'h01 ;	 	 	//  broadcast
		//i_regf_RnW_tb 		= 1'b0 ;  	 	// write 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor both tested 
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		// finish 
		DDR_clk_wait(50);
		i_frmcnt_last_frame_tb = 1'b0 ;

		////////////////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////////




		// test case 2 Broadcast with regular and even number of data bytes (4 bytes) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		/* second test case  : braodcast sequence
							   regular  
							   even number of bytes
		*/
		// configuration 
		i_regf_CMD_tb 	 	= 8'h01 ;	 	 	//  broadcast
		//i_regf_RnW_tb 		= 1'b0 ;  	 	// write 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		/////////////// repeatd data 2 bytes ////////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////


		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;
		i_frmcnt_last_frame_tb = 1'b0 ;

		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		// finish 


		////////////////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////////
		DDR_clk_wait(49);
		sys_clk_wait(1);
		// test case 3 Broadcast with regular and odd number of data bytes (3 bytes) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		/* second test case  : braodcast sequence
							   regular  
							   even number of bytes
		*/
		// configuration 
		i_regf_CMD_tb 	 	= 8'h01 ;	 	 	//  broadcast
		//i_regf_RnW_tb 		= 1'b0 ;  	 	// write 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		/////////////// repeatd data 2 bytes ////////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 



		i_frmcnt_last_frame_tb = 1'b1 ;





		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////


		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		// finish 


		
		////////////////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////////
		DDR_clk_wait(49);
		sys_clk_wait(1);
		// test case 4 Direct with regular and odd number of data bytes (3 bytes) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		/* second test case  : braodcast sequence
							   regular  
							   even number of bytes
		*/
		// configuration 
		i_regf_CMD_tb 	 	= 8'h90 ;	 	 	// Direct
		i_regf_RnW_tb 		= 1'b0 ;  	 	    // write 
		i_regf_DEV_INDEX_tb = 5'd6 ;			// 7th target 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////// CRC ////////////////////

		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;



		//////////////////////////// second comand word //////////////////////////


		// special preamble 
		DDR_clk_wait(2);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


//


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		

		


		////////////////////////////////   repeated data  //////////////////////////////
		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 



		i_frmcnt_last_frame_tb = 1'b1 ;





		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		//////////////////// CRC ////////////////////////////


		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		// finish 


		//DDR_clk_wait(50);

		////////////////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////////


		DDR_clk_wait(49);
		sys_clk_wait(1);
		// test case 5 Direct with regular and even number of data bytes (4 bytes) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		/* second test case  : Direct sequence
							   regular  
							   even number of bytes
		*/
		// configuration 
		i_regf_CMD_tb 	 	= 8'h90 ;	 	 	// Direct
		i_regf_RnW_tb 		= 1'b0 ;  	 	    // write 
		i_regf_DEV_INDEX_tb = 5'd6 ;			// 7th target 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////// CRC ////////////////////

		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;



		//////////////////////////// second comand word //////////////////////////


		// special preamble 
		DDR_clk_wait(2);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


//


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		

		


		////////////////////////////////   repeated data  //////////////////////////////
		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 



		i_frmcnt_last_frame_tb = 1'b0 ;





		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		i_frmcnt_last_frame_tb = 1'b0 ;


		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		//////////////////// CRC ////////////////////////////


		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;


		DDR_clk_wait(49);
		sys_clk_wait(1);
		////////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////
		// test case 6 Direct with immediate and no defining no data bytes (DTT = 0) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		
		// configuration 
		i_regf_CMD_tb 	 	= 8'h90 ;	 	 	// Direct
		i_regf_RnW_tb 		= 1'b0 ;  	 	    // write 
		i_regf_DEV_INDEX_tb = 5'd6 ;			// 7th target 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		//i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd1 ; 		    // 0 regular  , 1 immediate 
		i_regf_DTT_tb 		= 3'd0 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		i_frmcnt_last_frame_tb = 1'b1 ;
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////// CRC ////////////////////

		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


/*
		//////////////////////////// second comand word //////////////////////////


		// special preamble 
		DDR_clk_wait(2);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


//


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		

		


		////////////////////////////////   repeated data  //////////////////////////////
		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b1 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 



		i_frmcnt_last_frame_tb = 1'b0 ;





		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		i_frmcnt_last_frame_tb = 1'b0 ;


		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		//////////////////// CRC ////////////////////////////


		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;
*/

		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;

		DDR_clk_wait(49);
		sys_clk_wait(1);

		///////////////////////////////////////////////////// PASSED /////////////////////////////////////////////////////////////////
		// test case 7 Direct with regular and even number of data bytes (4 bytes) 

		// first things first 
		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b1 ;
		
		
		// configuration 
		i_regf_CMD_tb 	 	= 8'h90 ;	 	 	// Direct
		i_regf_RnW_tb 		= 1'b1 ;  	 	    // read 
		i_regf_DEV_INDEX_tb = 5'd6 ;			// 7th target 
		i_regf_TOC_tb 		= 1'b0 ; 	 	 	// not the last command discriptor
		i_regf_WROC_tb 		= 1'b0 ; 	 		// response status is not required 
		i_regf_DBP_tb 		= 1'b1 ; 	 	 	// defining byte is not present 
		i_regf_SRE_tb 		= 1'b0 ; 	 		// short read is not considered as error 
		i_regf_CMD_ATTR_tb  = 3'd0 ; 		    // 0 regular  , 1 immediate 
		//i_regf_DTT_tb 		= 3'd2 ; 	 	// only 2 payload without defining byte 
		
		i_sclstall_stall_done_tb = 1'b0 ;

		// special preamble 
		DDR_clk_wait(2);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 CCC value 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 8 ZEROS 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////// CRC ////////////////////

		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;



		//////////////////////////// second comand word //////////////////////////


		// special preamble 
		DDR_clk_wait(2);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// Rnw 1 bit = 0.5 DDr

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 reserved bits == 6.5 DDR clk cycles
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 7 addres + 1 p.a == 7.5 DDR clk cycles
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


//


		//////////// repeatd data first 2 bytes /////////////////

		// 1 first preamble 
		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;


		// 1 second preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb	 	  = 1'b0 ; 	 	// ack
		i_rx_error_tb 	  = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		DDR_clk_not_pulse(i_rx_pre_tb);


		// 8 FIRST DATA BYTE 
		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;

		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		//i_frmcnt_last_frame_tb = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		/////////////////////////////////////////////////////////

		

		


		////////////////////////////////   repeated data  //////////////////////////////
		// 1 first preamble 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_rx_pre_tb = 1'b1 ;
		i_rx_error_tb = 1'b0 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		//DDR_clk_not_pulse(i_rx_pre_tb);

		// 1 second preamble 
		$display($time);

		sys_clk_wait(1);
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		//DDR_clk_not_pulse(i_rx_pre_tb);
		i_rx_pre_tb = 1'b0 ;

		// 8 FIRST DATA BYTE 



		i_frmcnt_last_frame_tb = 1'b0 ;





		DDR_clk_wait(6);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;


		// 8 SECOND DATA BYTE 
		DDR_clk_wait(7);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;
		i_frmcnt_last_frame_tb = 1'b0 ;


		// 2 parity == 1.5 DDR clk cycles
		DDR_clk_wait(1);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		i_frmcnt_last_frame_tb = 1'b0 ; 						/////////////////// deh lw7dha test case (abort by target vs matched length of data)
		system_clk_pulse(i_rx_mode_done_tb) ;
		//system_clk_pulse(i_frmcnt_last_frame_tb) ;

		//////////////////// CRC ////////////////////////////

/*
		// crc prea
		DDR_clk_wait(1); 
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;

*/

		///// crc preamble /////
		sys_clk_wait(1);
		i_rx_pre_tb = 1'b1 ;
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;

		sys_clk_wait(1);
		i_rx_pre_tb = 1'b0 ;
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;







		///////////////////////


		// C token 
		DDR_clk_wait(3);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;

		// checksum
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_rx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_rx_mode_done_tb) ;

		// restart pattern 
		DDR_clk_wait(5);
		sys_clk_wait(1);
		i_sclstall_stall_done_tb = 1'b1 ;
		i_tx_mode_done_tb = 1'b1 ;
		system_clk_pulse(i_tx_mode_done_tb) ;
		DDR_clk_pulse(i_sclstall_stall_done_tb) ;


		@(posedge i_sys_clk_tb)
		i_engine_en_tb = 1'b0 ;
		i_frmcnt_last_frame_tb = 1'b0 ;


		DDR_clk_wait(49);
		sys_clk_wait(1);

		// finish 
		//DDR_clk_wait(50);
































































		
		$stop ;
	end





	task system_reset ;
		begin 
			@(negedge i_sys_clk_tb)
			i_rst_n_tb = 1'b0 ;
			#(CLK_PERIOD) i_rst_n_tb = 1'b1 ;
		end 
	endtask

	task system_clk_pulse (inout logic pulse_signal) ;
		begin 
			//pulse_signal = 1'b1 ;
			#(CLK_PERIOD) pulse_signal = 1'b0 ;
		end 
	endtask

	task DDR_clk_pulse (inout logic pulse_signal );
		begin 
			//pulse_signal = 1'b1 ;
			#(DDR_CLK_PERIOD) pulse_signal = 1'b0 ;
		end 
	endtask

	task DDR_clk_wait (input logic [15:0] no_of_cycles);
		begin 
			repeat(no_of_cycles) begin
				#(DDR_CLK_PERIOD);
			end
		end 
	endtask

	task sys_clk_wait (input logic [15:0] no_of_cycles);
		begin 
			repeat(no_of_cycles) begin
				#(CLK_PERIOD);
			end
		end 
	endtask

	task DDR_clk_not_pulse (inout logic not_pulse_signal);
		begin 
			#(DDR_CLK_PERIOD) not_pulse_signal = 1'b1 ;
		end 
	endtask

endmodule 
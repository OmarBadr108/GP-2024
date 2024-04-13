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
	wire [3:0] i_stall_cycles ;

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

	CCC_Handler DUT0 (
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
		.o_sclstall_code(i_stall_cycles),
		.o_tx_en(o_tx_en_tb),
		.o_tx_mode(o_tx_mode_tb),
		.o_rx_en_negedge(o_rx_en_tb),
		.o_rx_mode_negedge(o_rx_mode_tb),
		.o_bitcnt_en(i_bitcnt_en_tb),
		.o_bitcnt_err_rst(o_bitcnt_err_rst_tb),
		.o_frmcnt_en(o_frmcnt_en_tb),
		.o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb), 	 	 	 	 	 	 // 

		.o_frmcnt_Direct_Broadcast_n(o_frmcnt_Direct_Broadcast_n_tb),

		.o_regf_wr_en(o_regf_wr_en_tb),
		.o_regf_rd_en(o_regf_rd_en_tb),
		.o_regf_addr(o_regf_addr_tb),
		.o_engine_done(o_engine_done_tb),
		.o_txrx_addr_ccc(o_txrx_addr_ccc_tb),
		.o_engine_odd(o_engine_odd_tb),
		.o_regf_ERR_STATUS(o_regf_ERR_STATUS_tb)
		);




	scl_generation DUT1 (
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


		bits_counter DUT2 (
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
		


		frame_counter DUT3 (
		//.i_fcnt_no_frms (i_fcnt_no_frms_tb),
		.i_fcnt_clk (i_sys_clk_tb),
		.i_fcnt_rst_n (i_rst_n_tb),
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
		 
		 scl_staller DUT4 (
		 .i_stall_clk(i_sys_clk_tb), 
		 .i_stall_rst_n(i_rst_n_tb),
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

		 
		 reg_file DUT5 (
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
			.i_mux_zero(i_regf_data_wr_tb),
			.i_selector(my_regf_data_wr_tb_selector),
			.o_mux_out(my_regf_data_wr_tb_mux_out)
			);

		mux  #(.WIDTH(12)) DUT8 (
			.i_mux_one(my_regf_addr_tb),
			.i_mux_zero(o_regf_addr_tb),
			.i_selector(my_regf_addr_tb_selector),
			.o_mux_out(my_regf_addr_tb_mux_out)
			);


		reg       i_sdahnd_rx_sda_tb ;
		reg 	  i_crc_value_tb ;
		reg  	  i_crc_valid_tb ;
		wire      o_crc_data_valid_tb ;
		wire  	  o_ddrccc_error_done_tb ;
		wire  	  o_crc_en_tb ;

		RX DUT9 (
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
			
		.o_regfcrc_rx_data_out		(i_regf_data_wr_tb)			,
		.o_ddrccc_rx_mode_done		(i_rx_mode_done_tb)			,
		.o_ddrccc_pre				(i_rx_pre_tb)				,
		.o_ddrccc_error				(i_rx_error_tb)				,
		.o_crc_en					(o_crc_en_tb)               , // 
		.o_crc_data_valid           (o_crc_data_valid_tb)       ,
		.o_ddrccc_error_done   	    (o_ddrccc_error_done_tb)      

);
    	reg  [4:0] i_crc_crc_value_tb ;
    	wire       o_sdahnd_serial_data_tb ;
    	wire [7:0] o_crc_parallel_data_tb ;

    	tx DUT10 (
		.i_sys_clk 				 (i_sys_clk_tb),
		.i_sys_rst 				 (i_rst_n_tb),
		.i_ddrccc_tx_en 		 (o_tx_en_tb),
		.i_sclgen_scl_pos_edge 	 (scl_pos_edge_tb),
		.i_sclgen_scl_neg_edge 	 (scl_neg_edge_tb),
		.i_ddrccc_tx_mode 		 (o_tx_mode_tb),
		.i_regf_tx_parallel_data (i_regf_tx_parallel_data_tb),
		.i_ddrccc_special_data 	 (i_regf_CMD_tb),
		.i_crc_crc_value 		 (i_crc_crc_value_tb),
		.o_sdahnd_serial_data 	 (o_sdahnd_serial_data_tb),
		.o_ddrccc_mode_done 	 (i_tx_mode_done_tb),
		.o_crc_parallel_data 	 (o_crc_parallel_data_tb),
		.o_crc_en 				 (o_crc_en_tb)
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

    	integer i ;

// 4-initial block 
/* IMPORTANT NOTES :
		1- (General) when driving input to the block which is considered as output of other block u must drive it at posedge not at negdge .
		2- (specifically for our system) : to predict the time to set the tx mode done u count like that >>
				(no. of SCL_DDR clk cycle - 1) + 1 sys clk  

*/
	// for second preamble and read data 
	initial begin 
		forever begin 
			#(2*CLK_PERIOD) i_sdahnd_rx_sda_tb = $random() ;
		end 
	end 


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
		i_crc_value_tb 			  = 'd0 ;
		i_crc_crc_value_tb 		  = 'd0 ;
		i_crc_valid_tb 			  = 'd1 ;
		
		#(5*CLK_PERIOD);
		

		// initialization of the object 
		conf_obj = new();

		for (i=0 ; i<1000 ; i++) begin

			assert(conf_obj.randomize()); // "lw feh moshkla fel constrains edeny error" deh lazmet the word assert

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
		end	
		$stop ;
	end



	task system_reset ;
		begin 
			@(negedge i_sys_clk_tb)
			i_rst_n_tb = 1'b0 ;
			#(CLK_PERIOD) i_rst_n_tb = 1'b1 ;
		end 
	endtask
/*
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
*/
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
endmodule 
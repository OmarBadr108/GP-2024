module scl_generation_bits_counter_tb ();

/*
1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .
*/ 


// 1-signal declaration 
	// common signals 
	reg        i_sys_clk_tb = 0 , i_rst_n_tb  ;

	// scl generation signals
	reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb , i_cccnt_err_rst_tb;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb , o_scl_tb ;

	// bits counter signals 
	reg  	   i_bitcnt_en_tb ;
	wire [5:0] o_cnt_bit_count_tb ;

	// frame counter signals 
	reg  	   i_fcnt_clk_tb = 0 , i_fcnt_rst_n_tb ;
	reg [7:0]  i_fcnt_no_frms_tb 	  ;
	reg 	   o_frmcnt_en_tb         ;
	reg 	   i_regf_CMD_ATTR_tb     ;
	reg [15:0] i_regf_DATA_LEN_tb     ;
	reg [2:0]  i_regf_DTT_tb          ;
	wire 	   o_cccnt_last_frame_tb  ; // ours
	wire 	   o_fcnt_last_frame_tb   ;  	// sdr
  
// 2-clk generation 

	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;

	// frame counter clk = 25 MHZ == SCL clk 
	parameter FRAME_COUNTER_CLK_PERIOD = 40 ; 	 	 	 
	always #(FRAME_COUNTER_CLK_PERIOD/2) i_fcnt_clk_tb = ~i_fcnt_clk_tb ;

	parameter FRAME_PERIOD = 40 * CLK_PERIOD ;

// 3-DUT instatiation 
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
		.i_cccnt_err_rst (i_cccnt_err_rst_tb), 

		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);

		frame_counter DUT2 (
		.i_fcnt_no_frms (i_fcnt_no_frms_tb),
		.i_fcnt_clk (i_fcnt_clk_tb),
		.i_fcnt_rst_n (i_fcnt_rst_n_tb),
		.i_fcnt_en (o_frmcnt_en_tb),
		.i_regf_CMD_ATTR (i_regf_CMD_ATTR_tb),
		.i_regf_DATA_LEN (i_regf_DATA_LEN_tb),
		.i_regf_DTT (i_regf_DTT_tb),
		.i_cnt_bit_count (o_cnt_bit_count_tb),

		.o_fcnt_last_frame (o_fcnt_last_frame_tb),
		.o_cccnt_last_frame (o_cccnt_last_frame_tb)

	);

// 4-initial block 
	initial begin 
		// time zero 
		i_rst_n_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		i_sdr_scl_gen_pp_od_tb = 1'b1 ;
		i_cccnt_err_rst_tb 	   = 1'b0 ;
		i_bitcnt_en_tb   	   = 1'b0 ; 
		i_fcnt_rst_n_tb   	   = 1'b1 ;
		//frame counter 
   	  
		o_frmcnt_en_tb  	   = 1'b0 ;      
		i_regf_CMD_ATTR_tb     = 1'b0 ; // regular 
		i_regf_DATA_LEN_tb     = 16'd8 ;
		i_regf_DTT_tb          = 3'd3 ; 
	

		#(6*CLK_PERIOD);
		i_rst_n_tb    = 1'b0 ; // asserted
		i_fcnt_rst_n_tb = 1'b0 ;

		#(5*CLK_PERIOD); 
		i_fcnt_rst_n_tb = 1'b1 ; // not asserted
		#(6*CLK_PERIOD);
		i_rst_n_tb    = 1'b1 ; // not asserted

		#(4*CLK_PERIOD);
		i_bitcnt_en_tb   	   = 1'b1 ; 
		o_frmcnt_en_tb  	   = 1'b1 ;      
		i_regf_CMD_ATTR_tb     = 1'b0 ; // regular 
		i_regf_DATA_LEN_tb     = 16'd8 ; // 
		i_regf_DTT_tb          = 3'd3 ;
		

		#(8*FRAME_PERIOD);

		#(50*CLK_PERIOD);

		$stop ;
	end
endmodule 
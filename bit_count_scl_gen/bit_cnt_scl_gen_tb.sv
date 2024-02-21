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
	reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
	wire 	   scl_pos_edge_tb , scl_neg_edge_tb , o_scl_tb ;

	// bits counter signals 
	reg  	   i_bitcnt_en_tb ;
	wire [4:0] o_cnt_bit_count_tb ;

// 2-clk generation 

	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;


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
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);

// 4-initial block 
	initial begin 
		// time zero 
		i_rst_n_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		i_sdr_scl_gen_pp_od_tb = 1'b1 ;

		i_bitcnt_en_tb   	   = 1'b1 ; 


		#(3*CLK_PERIOD);
		i_rst_n_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_rst_n_tb    = 1'b1 ; // not asserted



		#(500*CLK_PERIOD);
		$stop ;
	end
endmodule 
module scl_generation_tb ();
// 5lek faker ya 3zezy awl ma tsm3 testbench egy f balk 4 7agat
/*

1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .

*/ 


// 1-signal declaration 
	reg        i_sdr_ctrl_clk_tb = 0 , i_sdr_ctrl_rst_n_tb  , i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb  ;
	wire 	   o_scl_pos_edge_tb , o_scl_neg_edge_tb , o_scl_tb ;

// 2-clk generation 

	//  1- system clk = 50 Mhz
	parameter CLK_PERIOD = 10 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sdr_ctrl_clk_tb = ~i_sdr_ctrl_clk_tb ;


// 3-DUT instatiation 
	scl_generation DUT (
		.i_sdr_ctrl_clk      (i_sdr_ctrl_clk_tb),
		.i_sdr_ctrl_rst_n 	 (i_sdr_ctrl_rst_n_tb),
		.i_sdr_scl_gen_pp_od (1'b1),
		.i_scl_gen_stall  	 (i_scl_gen_stall_tb),
		.i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb),
		.i_timer_cas         (i_timer_cas_tb),
		.o_scl_pos_edge      (o_scl_pos_edge_tb),
		.o_scl_neg_edge      (o_scl_neg_edge_tb),
		.o_scl 	 			 (o_scl_tb)
		
	);

// 4-initial block 
	initial begin 
		// time zero 
		i_sdr_ctrl_rst_n_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;


		#(3*CLK_PERIOD);
		i_sdr_ctrl_rst_n_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_sdr_ctrl_rst_n_tb    = 1'b1 ; // not asserted



		#(500*CLK_PERIOD);
		$stop ;
	end
endmodule 
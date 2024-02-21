module bits_counter_tb ();
// 5lek faker ya 3zezy awl ma tsm3 testbench egy f balk 4 7agat
/*

1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .

*/ 


// 1-signal declaration 
	reg        i_sys_clk_tb = 0 , i_rst_n_tb , i_bitcnt_en_tb , i_scl_pos_edge_tb , i_scl_neg_edge_tb , i_scl_clk_tb ;
	wire [4:0] o_cnt_bit_count_tb ;

// 2-clk generation 

	//  1- system clk = 50 Mhz
	parameter SYS_CLK_PERIOD = 10 ; 	 	 	 
	always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;


	//  2 - SCL Clk = 12.5 Mhz
	parameter SCL_CLK_PERIOD = 40 ; 	 	 	 
	always #(CLK_PERIOD/2) i_scl_clk_tb = ~i_scl_clk_tb ;


	// scl pos edge logic
	initial begin 
		if (i_sys_clk_tb && i_scl_clk_tb) begin 
			i_scl_pos_edge_tb = 1'b1 ;
		end 
	end 

// 3-DUT instatiation 
	bits_counter DUT (
		.i_sys_clk       (i_sys_clk_tb),
		.i_rst_n 	     (i_rst_n_tb),
		.i_bitcnt_en     (i_bitcnt_en_tb),
		.i_scl_pos_edge  (i_scl_pos_edge_tb),
		.i_scl_neg_edge  (i_scl_neg_edge_tb),
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	);

// 4-initial block 
	initial begin 
		// time zero 
		// we r assigned to follow a defined input pattern in the question which is(10011) .. mn el 4mal lel ymen :)

		// first test case in any sequential design is testing reset
		rst_n_tb = 1'b0 ; // asserted (active low 34an   _n   )
		# (3*CLK_PERIOD);
		rst_n_tb = 1'b1 ; // de-asserted
		# (3*CLK_PERIOD);

		// 1
		@(negedge clk_tb) // input new stimulus
		fsm_in_tb = 1'b1 ; 
		#(CLK_PERIOD/4); // checking mealy behavior
		if (fsm_out_tb != 2'b11) begin // checking output
			$display("error in first input (from a to b)",$time);
		end 

		// 0
		@(negedge clk_tb) // input new stimulus
		fsm_in_tb = 1'b0 ; 
		#(CLK_PERIOD/4); // checking mealy behavior
		if (fsm_out_tb != 2'b10) begin // checking output
			$display("error in second input (from b to c)",$time);
		end

		// 0
		@(negedge clk_tb) // input new stimulus
		fsm_in_tb = 1'b0 ; 
		#(CLK_PERIOD/4); // checking mealy behavior
		if (fsm_out_tb != 2'b11) begin // checking output
			$display("error in first input (from c to a)",$time);
		end


		// 1
		@(negedge clk_tb) // input new stimulus
		fsm_in_tb = 1'b1 ; 
		#(CLK_PERIOD/4); // checking mealy behavior
		if (fsm_out_tb != 2'b11) begin // checking output
			$display("error in first input (from a to b)",$time);
		end

		// 1
		@(negedge clk_tb) // input new stimulus
		fsm_in_tb = 1'b1 ; 
		#(CLK_PERIOD/4); // checking mealy behavior
		if (fsm_out_tb != 2'b01) begin // checking output
			$display("error in first input (from b to d)",$time);
		end

		#(5*CLK_PERIOD);
		$stop ;
	end
endmodule 
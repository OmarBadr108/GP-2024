timesacle 1ns / 1ps 
module restart_exit_test ();

reg i_sdr_ctrl_clk = 0  ;     
reg i_sdr_ctrl_rst_n    ;   
reg i_sdr_scl_gen_pp_od ;
reg i_scl_gen_stall     ;
reg i_sdr_ctrl_scl_idle ;
reg i_timer_cas         ;

wire o_scl_pos_edge      ;
wire o_scl_neg_edge      ;
wire o_scl               ;

parameter CLK_PERIOD = 20 ;

reg [4:0] i_stall_cycles ;
wire o_stall_done   ;  
wire o_scl_stall    ;


scl_staller scl_staller_dut (.i_stall_clk(i_sdr_ctrl_clk)     ,
							 .i_stall_rst_n(i_sdr_ctrl_rst_n) ,
							 .i_stall_flag(i_scl_gen_stall)   ,
							 .i_stall_cycles(i_stall_cycles)  ,
							 .o_stall_done(o_stall_done)      ,
							 .o_scl_stall (o_scl_stall)							 
							 ) ;


scl_generation scl_generation (.*) ;

always #(CLK_PERIOD/2) i_sdr_ctrl_clk = ! i_sdr_ctrl_clk ;

	initial begin 
		i_sdr_scl_gen_pp_od = 1'b1 ;
		i_sdr_ctrl_scl_idle = 1'b0 ;
		i_timer_cas 		= 1'b0 ;
		
		i_stall_cycles = 18 ;

		i_sdr_ctrl_rst_n = 1'b0 ;
		#(3*CLK_PERIOD) ;
		i_sdr_ctrl_rst_n = 1'b1 ;
		#(3*CLK_PERIOD) ;



		#(102*CLK_PERIOD);
		i_scl_gen_stall = 1'b1 ;
		
		@(posedge o_stall_done) ;
		i_scl_gen_stall = 1'b0 ;

		#(5000) ;
		$stop;
	end 
endmodule
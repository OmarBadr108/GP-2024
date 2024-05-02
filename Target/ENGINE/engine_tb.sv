module Target_engine_tb ();
// signal declaration 
	reg 	  i_sys_clk = 0    ;
	reg 	  i_sys_rst 	   ;
	reg 	  i_rstdet_RESTART ; 
	reg 	  i_exitdet_EXIT   ;
	reg 	  i_ENTHDR_done    ;
	reg  	  i_CCC_done 	   ; 
	reg 	  i_NT_done 	   ;
	reg [1:0] i_rx_decision    ;
	reg 	  i_rx_decision_done ;

	wire [1:0] o_muxes     ;
	wire 	   o_ENTHDR_en ;
	wire 	   o_NT_en     ;
	wire 	   o_CCC_en    ;
	wire 	   o_rx_en     ;
	wire [3:0] o_rx_mode   ;

////////////////////////////////////////// RX Parameters ////////////////////////////////////////////////

parameter  [3:0]  initializing 			  = 4'b0000,  
                  pereamble 			  = 4'b0001, 
				  deserializing_data 	  = 4'b0010, 
				  deserializing_ccc_value = 4'b0011, 
				  check_Parity 			  = 4'b0100, 
				  token_CRC 			  = 4'b0101, 
				  CRC_value           	  = 4'b0110, 
				  deserializing_address   = 4'b0111, 
				  deserializing_zeros     = 4'b1000, 
				  special_pereamble       = 4'b1001; 

////////////////////////////////////////// decision Parameters //////////////////////////////////////////

parameter  [1:0]  not_me = 2'b00, 
                  me_ddr = 2'b01, 
				  CCC 	 = 2'b10, 
				  error  = 2'b11;

//////////////////////////////////////////// muxes Parameters ///////////////////////////////////////////

parameter  [1:0]  engine = 2'b00, 
                  ddr_nt = 2'b01, 
				  ccc 	 = 2'b10; 

// Dut Instatiation
Target_engine DUT (.*); // instatiation by name	

// clk generation
parameter CLK_PERIOD = 20 ; 

always #(CLK_PERIOD/2) i_sys_clk = ~i_sys_clk ;

// initial block 
initial begin 
	system_reset() ;
	//IDLE_SDR STATE
	#(18*CLK_PERIOD) ; // SDR word
	if (o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ",
		$time,o_ENTHDR_en,o_NT_en,o_CCC_en,o_muxes);

	// INITIALIZE STATE
	@(posedge i_sys_clk) i_ENTHDR_done = 1'b1 ;
	#(CLK_PERIOD) i_ENTHDR_done = 1'b0 ;
	
	#(40*CLK_PERIOD) ; // DDR word
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine && o_rx_en && o_rx_mode == initializing ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ,o_rx_en = %1b ,o_rx_mode = %d",
		$time,o_ENTHDR_en,o_NT_en,o_CCC_en,o_muxes,o_rx_en ,o_rx_mode);


	i_rx_decision_done = 1'b1 ;
	i_rx_decision = not_me ;
	#(2*CLK_PERIOD) ;
	i_rx_decision_done = 1'b0 ;

	//IDLE_HDR STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	
	#(10* CLK_PERIOD); // random period 
	i_rstdet_RESTART = 1'b1 ;
	#(2*CLK_PERIOD) ;
	i_rstdet_RESTART = 1'b0 ;

	// INITIALIZE STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine && o_rx_en && o_rx_mode == initializing ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ,o_rx_en = %1b ,o_rx_mode = %d",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes, o_rx_en, o_rx_mode);
	#(40*CLK_PERIOD) ; // DDR word
	
	i_rx_decision_done = 1'b1 ;
	i_rx_decision = error ;
	#(2*CLK_PERIOD) ;
	i_rx_decision_done = 1'b0 ;

	//IDLE_HDR STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	
	#(10* CLK_PERIOD); // random period 
	i_rstdet_RESTART = 1'b1 ;
	#(2*CLK_PERIOD) ;
	i_rstdet_RESTART = 1'b0 ;

	// INITIALIZE STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine && o_rx_en && o_rx_mode == initializing ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ,o_rx_en = %1b ,o_rx_mode = %d",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes, o_rx_en, o_rx_mode);
	#(40*CLK_PERIOD) ; // DDR word
	
	i_rx_decision_done = 1'b1 ;
	i_rx_decision = me_ddr ;
	#(2*CLK_PERIOD) ;
	i_rx_decision_done = 1'b0 ;

	// DDR_NT STATE
	if (!o_ENTHDR_en && o_NT_en && !o_CCC_en && o_muxes == ddr_nt ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	#(40*CLK_PERIOD) ; // DDR word

	i_NT_done = 1'b1 ;
	#(2*CLK_PERIOD) ; 
	i_NT_done = 1'b0 ;

	//IDLE_HDR STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	#(20*CLK_PERIOD) ; // randome time wait for another call 
	
	i_rstdet_RESTART = 1'b1 ;
	#(2*CLK_PERIOD) ;
	i_rstdet_RESTART = 1'b0 ;

	// INITIALIZE STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine && o_rx_en && o_rx_mode == initializing ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ,o_rx_en = %1b ,o_rx_mode = %d",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes, o_rx_en, o_rx_mode);
	#(40*CLK_PERIOD) ; // DDR word

	i_rx_decision_done = 1'b1 ;
	i_rx_decision = CCC ;
	#(2*CLK_PERIOD) ;
	i_rx_decision_done = 1'b0 ;

	// CCC_HANDLER STATE
	if (!o_ENTHDR_en && !o_NT_en && o_CCC_en && o_muxes == ccc ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	#(40*CLK_PERIOD) ; // DDR word

	i_CCC_done = 1'b1 ;
	#(2*CLK_PERIOD) ; 
	i_CCC_done = 1'b0 ;

	//IDLE_HDR STATE
	if (!o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine ) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b",
		$time,o_ENTHDR_en, o_NT_en, o_CCC_en, o_muxes);
	#(20*CLK_PERIOD) ; // randome time wait for another call 

	i_exitdet_EXIT = 1'b1 ;
	#(2*CLK_PERIOD) ; 
	i_exitdet_EXIT = 1'b0 ;

	//IDLE_SDR STATE
	#(18*CLK_PERIOD) ; // SDR word
	if (o_ENTHDR_en && !o_NT_en && !o_CCC_en && o_muxes == engine) $display("tamam",$time);
	else $display("time : %t mesh tamam : o_ENTHDR_en = %1b , o_NT_en = %1b , o_CCC_en = %1b , o_muxes = %2b ",
		$time,o_ENTHDR_en,o_NT_en,o_CCC_en,o_muxes);
	

	#(50*CLK_PERIOD);
	$stop ;

end 


task system_reset ;
	begin 
		@(negedge i_sys_clk)
		i_sys_rst = 1'b0 ;
		#(CLK_PERIOD) i_sys_rst = 1'b1 ;
	end 
endtask

endmodule
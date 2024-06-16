import SYSTEM_PACKAGE ::*;
`timescale 1us / 1ps
`default_nettype none


module I3C_TOP_TB ();

//-----------------------------Testbench signals-------------------------------------//
  logic         i_sdr_clk_tb           		; // system clk
  logic         i_sdr_rst_n_tb         		; // asynch neg edge reset
  logic         i_controller_en_tb     		; // from device configuration of Controller/Target role
  logic         i_i3c_i2c_sel_tb       		; // sdr/i2c blocks selector
  logic         i_ccc_en_dis_hj_tb     		; //2023: (TBD) for enable/disable events to prevent Bus-Initialization or DAA interruptions.
    
  logic         i_sclgen_rst_n_tb          	; // new by badr 

// Configurations signals
  logic [7:0]   i_regf_config_tb           	;
  logic         i_data_config_mux_sel_tb   	;  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
  logic [11:0]  i_regf_wr_address_config_tb	;
  logic         i_regf_wr_en_config_tb     	;
  logic         i_regf_rd_en_config_tb     	;

  wire          sda_tb                     	; // sda line
    
  logic         scl_tb                     	; // scl bus
  logic         o_sdr_rx_valid_tb          	; // output to host >> valid data are loaded    //2023
  logic         o_ctrl_done_tb              ; //2023

//-----------------------------Internal signals -------------------------------------//
logic sda_drive;
bit frame_ended;
int cycle_count ;
logic configuration_done=0;

//-----------------------------Parameters-------------------------------------//
    parameter CLK_PERIOD  = 10;
    parameter configuration   = 1'b1 ;
    parameter Design          = 1'b0 ;
    parameter config_location = 12'd1000 ;

    parameter EXPECTED_BROADCAST = 8'b11111100; // 'h7E+ R/W bit = 0
    parameter EXPECTED_ENTHDR0 = 9'b001000000;
    
    reg [2:0] RAND_CMD_ATTR  = 'd1   ;  // immediate data transfer command, dword1 is: data_byte4,3,2,1(def_byte)
    reg [3:0] RAND_TID       = 'd3   ;
    reg [7:0] RAND_CMD       = 8'h00 ;
 // reg       RAND_CP        = 1     ;
 	reg       RAND_CP;
 		
    reg [4:0] RAND_DEV_INDEX = 'd3   ;
    reg [1:0] RAND_RESERVED  = 'd0   ;
    reg [2:0] RAND_DTT       = 'd2   ;
    reg [2:0] RAND_MODE      = 'd6   ;
    reg       RAND_RnW       = 1'b0  ; // 0 for write ,  1 for read   
    reg       RAND_WROC      = 1'd0  ;
    reg       RAND_TOC               ;
    reg [7:0] RAND_DEF_BYTE  = 8'b0000_0000   ;    //'d1
    reg [7:0] RAND_DATA_TWO  = 8'b1111_0010   ; //'d2
    reg [7:0] RAND_DATA_THREE= 'd3   ; // DATA_LENGTH = {RAND_DATA_FOUR,RAND_DATA_THREE}
    reg [7:0] RAND_DATA_FOUR = 'd4   ;

//----------------------------- Clock Generation-------------------------------------//
always #(CLK_PERIOD/2) i_sdr_clk_tb = ~i_sdr_clk_tb;

//-----------------------------  Initial block  -------------------------------------//
// locally driven value
assign sda_tb   = sda_drive 			;

initial begin

	initialize();
	reset();


	//<-------------------------TEST CASE 1 ----------------------->//
	//<            Mode --> HDR, TOC = 0, CP = 1 (CCC) ,Broadcast CCC :ENEC       >//
	RAND_CP        = 1'b1     ;
	RAND_TOC       = 1'b0  ;

  	// change mux selector to write configurations
		switch_muxes(configuration);
		write_configurations();

	// change mux selector to give the regfile inputs control to design
		switch_muxes(Design);

	configuration_done = 1'b1;
	#(CLK_PERIOD)
	configuration_done = 1'b0;

	i_i3c_i2c_sel_tb    = 1'b1;
    i_controller_en_tb = 1'b1;
		 
    check_output(); //temporary to check enthdr ccc output

	// first second preamble for data word
	@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  	#(4*CLK_PERIOD)
    sda_drive = 'bz;

	// second second preamble for repeated data word
	#(CLK_PERIOD)
	@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b1;
  	#(4*CLK_PERIOD)
    sda_drive = 'bz;    

//@(posedge o_ctrl_done_tb)
//i_controller_en_tb = 1'b0;


	//<-------------------------TEST CASE 2 ----------------------->//
	//<            Mode --> HDR, TOC = 1(exit), CP = 1 (CCC) ,Direct CCC :ENEC       >//

    RAND_CMD       = 8'h80 ;
    RAND_TOC       = 1'b1  ;	
    configuration_done = 0;

	#(CLK_PERIOD)
   @(DUT.frame_counter_hdr.o_cccnt_last_frame == 'b1)
   
  
  // change mux selector to write configurations
	switch_muxes(configuration);
	write_configurations();

	// change mux selector to give the regfile inputs control to design
	switch_muxes(Design);
	configuration_done = 1'b1;
	#(CLK_PERIOD)
	configuration_done = 1'b0;

	i_i3c_i2c_sel_tb  = 1'b1;
    i_controller_en_tb 	= 1'b1;	
    //check_output(); //temporary to check enthdr ccc output

#(CLK_PERIOD)
    // first data word preamble
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;


#(CLK_PERIOD)
    // second data word preamble
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;    

/*
    //////////// added by badr ////////////////
	//<-------------------------TEST CASE 3 ----------------------->//
	//<            Mode --> HDR, TOC = 1(exit), CP = 1 (CCC) ,Direct CCC :ENEC       >//

    RAND_CMD       = 8'h80 ;
    RAND_TOC       = 1'b1  ;	
    configuration_done = 0;

	#(CLK_PERIOD)
    @(DUT.frame_counter_hdr.o_cccnt_last_frame == 'b1)
   
  
  // change mux selector to write configurations
	switch_muxes(configuration);
	write_configurations();

	// change mux selector to give the regfile inputs control to design
	switch_muxes(Design);
	configuration_done = 1'b1;
	#(CLK_PERIOD)
	configuration_done = 1'b0;

	i_i3c_i2c_sel_tb  = 1'b1;
    i_controller_en_tb 	= 1'b1;	
    //check_output(); //temporary to check enthdr ccc output

#(CLK_PERIOD)
    // first data word preamble
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;


#(CLK_PERIOD)
    // second data word preamble
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;    
*/





//@(DUT.tx.i_ddrccc_tx_mode == 15)
//DUT.CCC_Handler.i_sclstall_stall_done = 1;
 
 /* 

/////////////////////////////////////////////NT Test////////////////////////////////////////////////
								//<-------------------------TEST CASE 1 ----------------------->//
										//<            Mode --> HDR, TOC = 1, CP = 0 (NT)       >//
    RAND_CP                       = 0     ;
   	i_i3c_i2c_sel_tb     			    = 1'b1;
    i_controller_en_tb 						= 1'b1;

    check_output(); //temporary to check enthdr ccc output

		// first second preamble for data word
		@(posedge DUT.DDR_NT.o_rx_en )
			sda_drive = 'b0;
		  #(4*CLK_PERIOD)
		    sda_drive = 'bz;


    #(3*CLK_PERIOD)
		  @(posedge DUT.DDR_NT.o_rx_en )
			sda_drive = 'b0;
		  #(4*CLK_PERIOD)
		    sda_drive = 'bz;
*/




    #50000
    $stop;
end



	// deserialization checking 

	always @(DUT.CCC_Handler.current_state) begin 
		if (DUT.CCC_Handler.i_engine_en && DUT.CCC_Handler.current_state == RNW) begin 
			#(CLK_PERIOD) ;
			check_cmd_word();
		end 
	end 

	always @(DUT.CCC_Handler.current_state) begin 
		if (DUT.CCC_Handler.i_engine_en && DUT.CCC_Handler.current_state == CCC_BYTE) begin 
			#(CLK_PERIOD) ;
			check_CCC_value_data_word();
		end 
	end

	always @(DUT.CCC_Handler.current_state or DUT.DDR_NT.current_state) begin 
		if ((DUT.CCC_Handler.i_engine_en && DUT.CCC_Handler.current_state == FIRST_DATA_BYTE) || (DUT.DDR_NT.i_engine_en && DUT.DDR_NT.current_state == first_data_byte)) begin 
			#(CLK_PERIOD) ;
			check_repeated_data_word();
		end 
	end


	task check_cmd_word (); 
		begin 
			logic [17:0] collected_cmd_wrd ;
			bit 	     parity_adj_7e ,parity_adj ,P1_cmdword ,P0_cmdword ;
			bit   [17:0] correct_first_cmd_word , correct_cmd_word ;
			int 		 o ; // counter

			for ( o = 0 ; o < 'd18 ; o++ ) begin 

			@ (posedge DUT.scl_pos_edge or posedge DUT.scl_neg_edge ) ;

				collected_cmd_wrd['d17- o] = sda_tb ;

				//$display("nvlaue of SDA line is  %b : %t",sda_tb,$time);

				parity_adj_7e = (DUT.CCC_Handler.i_regf_RnW ^ (^7'h7E) ) ;
				parity_adj    = (DUT.CCC_Handler.i_regf_RnW ^ (^DUT.CCC_Handler.o_txrx_addr_ccc[6:0]) ) ;

				P1_cmdword    = DUT.CCC_Handler.i_regf_RnW ^ collected_cmd_wrd[9] ^ collected_cmd_wrd[7] ^ collected_cmd_wrd[5] ^ collected_cmd_wrd[3] ; // index is shifted by 2 as this is the 18 bit word (data + parity)
				P0_cmdword    =  1 ;

				correct_first_cmd_word = {1'b0 , 7'd0 , 7'h7E 					, parity_adj_7e , P1_cmdword , P0_cmdword } ;
				correct_cmd_word 	   = {1'b0 , 7'd0 , DUT.CCC_Handler.o_txrx_addr_ccc[6:0] , parity_adj    , P1_cmdword , P0_cmdword } ;

				# (2*CLK_PERIOD) ;
				if (o == 'd17) begin 
					if (DUT.CCC_Handler.first_time || !DUT.CCC_Handler.Direct_Broadcast_n_del) begin  // this is a 7E cmd word
						assert (correct_first_cmd_word == collected_cmd_wrd) $display("first command word in CCC is CORRECT : %0t" ,$time);
						else 												 $display("first command word in CCC is WRONG   : %0t" ,$time);
					end 
					else begin 	// this is an address word  
						assert (correct_cmd_word == collected_cmd_wrd) $display("second command word in CCC is CORRECT : %0t" ,$time);
						else 										   $display("second command word in CCC is WRONG   : %0t" ,$time);
					end 
				end  
			end 
		end  
	endtask 


	task check_CCC_value_data_word (); 
		begin 
			logic [17:0] collected_data_wrd ;
			bit 	     P1 ,P0 ;
			bit   [17:0] correct_first_data_word  ;
			int 		 o ; // counter 

			for ( o = 0 ; o < 'd18 ; o++ ) begin 

			@ (posedge DUT.scl_pos_edge or posedge DUT.scl_neg_edge ) ;

				collected_data_wrd['d17- o] = sda_tb ;

				//$display("vlaue of SDA line is  %b : %t",sda_tb,$time);

				P1 = collected_data_wrd[17] ^ collected_data_wrd[15] ^ collected_data_wrd[13] ^ collected_data_wrd[11] ^ collected_data_wrd[9] ^
				 	 collected_data_wrd[7] ^ collected_data_wrd[5] ^ collected_data_wrd[3] ;

				P0 = collected_data_wrd[16] ^ collected_data_wrd[14] ^ collected_data_wrd[12] ^ collected_data_wrd[10] ^ collected_data_wrd[8] ^
					 collected_data_wrd[6] ^ collected_data_wrd[4] ^ collected_data_wrd[2] ^ 1 ; 

				correct_first_data_word = { DUT.CCC_Handler.o_txrx_addr_ccc , 8'd0 ,  P1 , P0 } ;

				# (2*CLK_PERIOD) ;
				if (o == 'd17) begin 
					assert (correct_first_data_word == collected_data_wrd) $display("CCC data word is CORRECT : %0t" ,$time);
					else 												   $display("CCC data word is WRONG   : %0t" ,$time);
				end  
			end 
		end  
	endtask 



	task check_repeated_data_word (); 
		begin 
			logic [17:0] collected_data_wrd ;
			bit 	     P1 ,P0 ;
			bit   [17:0] correct_repeated_data_word  ;
			int 		 o ;
			bit   [7:0] tmp_D1 , tmp_D0 ;

			for ( o = 0 ; o < 'd18 ; o++ ) begin 

			@ (posedge DUT.scl_pos_edge or posedge DUT.scl_neg_edge ) ;

				collected_data_wrd['d17- o] = sda_tb ;

				//$display("vlaue of SDA line is  %b : %t",sda_tb,$time);

				P1 = correct_repeated_data_word[17] ^ correct_repeated_data_word[15] ^ correct_repeated_data_word[13] ^ correct_repeated_data_word[11] ^ correct_repeated_data_word[9] ^
				 	 correct_repeated_data_word[7] ^ correct_repeated_data_word[5] ^ correct_repeated_data_word[3] ;

				P0 = correct_repeated_data_word[16] ^ correct_repeated_data_word[14] ^ correct_repeated_data_word[12] ^ correct_repeated_data_word[10] ^ correct_repeated_data_word[8] ^
					 correct_repeated_data_word[6] ^ correct_repeated_data_word[4] ^ correct_repeated_data_word[2] ^ 1 ; 

				if (o == 'd3) begin                            // any arbitrary value btn 0 -> 7
					tmp_D1 = DUT.regf_data_rd ; 
				end
	
				if (o == 'd10) begin 	 	 	 	 	 	   // any arbitrary value btn 8 -> 15
					tmp_D0 = DUT.regf_data_rd ;
				end 

				correct_repeated_data_word = { tmp_D1 , tmp_D0 , P1 , P0 };

				# (2*CLK_PERIOD) ;
				if (o == 'd17) begin 
					correct_repeated_data_word = { tmp_D1 , tmp_D0 , P1 , P0 };
					assert (correct_repeated_data_word == collected_data_wrd) $display("repeated data word is CORRECT : %0t" ,$time);
					else 													  $display("repeated data word is WRONG   : %0t" ,$time);
				end  
			end 
		end  
	endtask 


pullup(sda_tb);
//-----------------------------     Tasks       -------------------------------------//

task reset;
	begin
	    i_sdr_rst_n_tb 		        = 1'b1;
		# (CLK_PERIOD)
		i_sdr_rst_n_tb 				= 1'b0; // activated
		# (CLK_PERIOD)
		i_sdr_rst_n_tb 				= 1'b1; // de-activated

	end	
	endtask

task initialize; 
	begin
		i_sdr_clk_tb 				= 1'b0;
		i_sdr_rst_n_tb 				= 1'b1;
		i_i3c_i2c_sel_tb        	= 1'b1;  //i3c mode
		i_controller_en_tb      	= 1'b0;
		i_ccc_en_dis_hj_tb      	= 1'b0;
		sda_drive 					= 1'bz;
		i_data_config_mux_sel_tb    = 1'b1;
		i_regf_rd_en_config_tb   	= 1'b0;								
    	i_regf_wr_en_config_tb   	= 1'b1;

	end
	endtask

task switch_muxes(input selector);
        begin 
            i_data_config_mux_sel_tb = selector ; // 1 for configuration and 0 for design 
        end 
    endtask 

task write_configurations();
	begin

//1.write randomized values
	// DWORD0
	 	i_regf_wr_en_config_tb = 1'b1;
	 #(2*CLK_PERIOD)																		    																									; 
		i_regf_config_tb     = { RAND_CMD[0] , RAND_TID , RAND_CMD_ATTR }  			 		;
    	i_regf_wr_address_config_tb = config_location 																												;
    	    
      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_CP , RAND_CMD[7:1] } 									;
    	i_regf_wr_address_config_tb = config_location + 'd1 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_DTT[0] , RAND_RESERVED , RAND_DEV_INDEX }  			;		    
    	i_regf_wr_address_config_tb = config_location + 'd2 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_TOC , RAND_WROC , RAND_RnW ,RAND_MODE , RAND_DTT[2:1]} ;
    	i_regf_wr_address_config_tb = config_location + 'd3 																									;

      // DWORD 1
       #(2*CLK_PERIOD)  																																									  ; 
		i_regf_config_tb     = RAND_DEF_BYTE     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd4 																									;		

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = RAND_DATA_TWO     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd5 																									;

       #(2*CLK_PERIOD); 																		 
		i_regf_config_tb     = RAND_DATA_THREE     																													;
    	i_regf_wr_address_config_tb  = config_location + 'd6 																									;

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = RAND_DATA_FOUR     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd7 																									;
  
        #(CLK_PERIOD) 																																											;
	end
endtask : write_configurations


task check_output ();
	begin
		logic [7:0] BROADCAST; // 7'h7E+ R/w bit
		logic [8:0] ENTHDR0; 

		BROADCAST = 8'b0; // 7'h7E+ R/w bit
		ENTHDR0 = 9'b0;
		// ddr code: 0x20 + T-bit
		//frame_ended = 1'b0;
		// once you see the start condition--> sample the first data 7E then sample 'h20 then the parity bit
		/*bit start_condition;
		start_condition = ~sda_tb &&  ~scl_tb 
		if(start_condition) begin
			data_check[i] <= //sda
		end
*/
			for(int i=0; i < 8 ; i++)   //receive first 8 bits of 7E and write bit
			 	begin  
				   @(posedge scl_tb)
				   	BROADCAST['d7 - i] = sda_tb;
			 	end

			@(negedge scl_tb)
			if(BROADCAST == EXPECTED_BROADCAST)
			 begin
					$display("Broadcast frame is received");
					send_ack();
			 end

			for(int i=0; i < 9 ; i++)   //receive first 8 bits of 7E and write bit
			 	begin  
				   @(posedge scl_tb)
				   	ENTHDR0['d8 - i] = sda_tb;
			 	end
 

			if(ENTHDR0 == EXPECTED_ENTHDR0) begin
				$display("ENTHDR frame is received");

				@(negedge scl_tb)
				#(CLK_PERIOD)
				frame_ended = 1'b1;
				#(CLK_PERIOD)
				frame_ended = 1'b0;


end	   		
		
	end 
endtask

task send_ack;
	begin
		//#(30*CLK_PERIOD)
		#(2*CLK_PERIOD)
			if(!scl_tb)       //drive ack when scl is low
			  begin  	
					sda_drive = 1'b0; //ack bit

				  @(negedge scl_tb)
				  //#(30*CLK_PERIOD)
				  #(2*CLK_PERIOD)  //(2*CLK_PERIOD)

						if(!scl_tb)
				 			sda_drive = 'bz;     
			  end
	end
endtask



//-----------------------------DUT Instantiation-------------------------------------//
I3C_TOP DUT (
 .i_sdr_clk           		(i_sdr_clk_tb)					, 
 .i_sdr_rst_n         		(i_sdr_rst_n_tb)				, 
 .i_controller_en     		(i_controller_en_tb)			, 
 .i_i3c_i2c_sel       		(i_i3c_i2c_sel_tb)				, 
 .i_ccc_en_dis_hj     		(i_ccc_en_dis_hj_tb)			, 
 .i_regf_config             (i_regf_config_tb)				,
 .i_data_config_mux_sel     (i_data_config_mux_sel_tb)		,    
 .i_regf_wr_address_config  (i_regf_wr_address_config_tb)	,
 .i_regf_wr_en_config       (i_regf_wr_en_config_tb)		,
 .i_regf_rd_en_config       (i_regf_rd_en_config_tb)        ,   
 .sda                 		(sda_tb)						,
 .scl                 		(scl_tb)						,
 .o_sdr_rx_valid      		(o_sdr_rx_valid_tb)				,
 .o_ctrl_done               (o_ctrl_done_tb)
 );

//-------------------------------------- Assertions ---------------------------------------//
	//assign sys_clk_50mhzzz = DUT.sys_clk_50mhz ;
/*
	property EXIT_and_stop_pattern ;
		@(posedge DUT.sys_clk_50mhz) (!scl_tb) [*3] |-> $fell(sda_tb) [*4] ##1 (!sda_tb && scl_tb) ##1 (sda_tb && scl_tb) ;
	endproperty
*/
	property EXIT_and_stop_pattern ;
		disable iff (!i_sdr_rst_n_tb) 
		@(posedge DUT.sys_clk_50mhz)
		(DUT.tx_mode_hdr_mux_out == exit_pattern && ($past(DUT.tx_mode_hdr_mux_out) != exit_pattern )) |=> 
																				   (!scl_tb &&  sda_tb) ##2
																				   (!scl_tb && !sda_tb) ##2
																				   (!scl_tb &&  sda_tb) ##2 
																				   (!scl_tb && !sda_tb) ##2 
																				   (!scl_tb &&  sda_tb) ##2 
																				   (!scl_tb && !sda_tb) ##2
																				   (!scl_tb &&  sda_tb) ##2 
																				   (!scl_tb && !sda_tb) ##1
																				   ( scl_tb && !sda_tb) ##1 
																				   ( scl_tb &&  sda_tb)     ;
	endproperty


	property Middle_Restart_pattern ;
		disable iff (!i_sdr_rst_n_tb) 
		@(posedge DUT.sys_clk_50mhz)
		(!DUT.frmcnt_last_frame_hdr && DUT.tx_mode_hdr_mux_out == restart_pattern && ($past(DUT.tx_mode_hdr_mux_out) != restart_pattern )) |-> 
																										##2
																				   (!scl_tb &&  sda_tb) ##2
																				   (!scl_tb && !sda_tb) ##2
																				   (!scl_tb &&  sda_tb) ##2 
																				   (!scl_tb && !sda_tb) ##1 
																				   (!scl_tb &&  sda_tb) ##1 
																				   ( scl_tb &&  sda_tb)     ;
	endproperty

	property Last_Restart_pattern ;
		disable iff (!i_sdr_rst_n_tb) 
		@(posedge DUT.sys_clk_50mhz)
		(DUT.frmcnt_last_frame_hdr && DUT.tx_mode_hdr_mux_out == restart_pattern && ($past(DUT.tx_mode_hdr_mux_out) != restart_pattern )) |-> 
																										##2
																				   (!scl_tb &&  sda_tb) ##2
																				   (!scl_tb && !sda_tb) ##2
																				   (!scl_tb &&  sda_tb) ##2 
																				   (!scl_tb && !sda_tb) ##1 
																				   (!scl_tb &&  sda_tb) ##1 
																				   ( scl_tb &&  sda_tb) ##1 
																				   ( scl_tb &&  sda_tb) ##1
																				   (!scl_tb &&  sda_tb)		;
	endproperty


	assert property(EXIT_and_stop_pattern) 
							$display("%t EXIT_and_stop_pattern SUCCEEDED ",$time); else
                            $display("%t EXIT_and_stop_pattern FAILED    ",$time);

    assert property(Middle_Restart_pattern) 
							$display("%t Middle_Restart_pattern SUCCEEDED ",$time); else
                            $display("%t Middle_Restart_pattern FAILED    ",$time);

    assert property(Last_Restart_pattern) 
							$display("%t Last_Restart_pattern SUCCEEDED ",$time); else
                            $display("%t Last_Restart_pattern FAILED    ",$time);












/*
// DUT.sys_clk_50mhz ;

    parameter scl_pos_wrt_sys_clc = 4 ;         // used in sdr transmission trancking changes every pos edge only of sda 
    parameter scl_pos_neg_wrt_sys_clc = 2 ;     // used in hdr transmission trancking changes every pos or neg edge of sda 

    //////////////////////////////////////////////////// ENTHDR assertion /////////////////////////////////////
    sequence start_bit_1 ;
        (sda_tb == 1'b1 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_2 ;
        start_bit_1 ##(1) (sda_tb == 1'b0 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_3 ;
        start_bit_2 ##(3) (sda_tb == 1'b0 && scl_tb == 1'b0 ); 
    endsequence

    sequence start_bit_4 ;
        start_bit_3 ##(1) (sda_tb == 1'b1 && scl_tb == 1'b0 ); 
    endsequence

    // end of START condition
    ////////////////////////////////////////////////////////////////////////

    sequence ENTHDR_1 ;                        // first bit of seven E is transmitted above and it's duration is here 
        start_bit_4 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_2 ;                       
        ENTHDR_1 ##(5*scl_pos_wrt_sys_clc) sda_tb == 1'b0 ;
    endsequence

    sequence ENTHDR_3 ;
        ENTHDR_2 ##(4*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_4 ;
        ENTHDR_3 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b0;
    endsequence

    sequence START_ENTHDR_sec;
        ENTHDR_4 ##(6*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ; // this is the first bit in the HDR mode i.e (RnW bit)
    endsequence



    // Property to track SDA line ENTHDR frame >> (8'b11111100 then 9'b001000000) then HDR 
    property START_ENTHDR_seq  ;
        @(posedge (DUT.sys_clk_50mhz)) $rose(i_controller_en_tb) |-> START_ENTHDR_sec ;  
    endproperty


    // Assert the property
    assert property(START_ENTHDR_seq)
                            $display("%t START_ENTHDR_sec PASSED ",$time); else
                            $display("%t START_ENTHDR_sec FAILED ",$time);


*/

endmodule






/*

`timescale 1us / 1ps
`default_nettype none


module I3C_TOP_TB ();

//-----------------------------Testbench signals-------------------------------------//
  logic         i_sdr_clk_tb           		; // system clk
  logic         i_sdr_rst_n_tb         		; // asynch neg edge reset
  logic         i_controller_en_tb     		; // from device configuration of Controller/Target role
  logic         i_i3c_i2c_sel_tb       		; // sdr/i2c blocks selector
  logic         i_ccc_en_dis_hj_tb     		; //2023: (TBD) for enable/disable events to prevent Bus-Initialization or DAA interruptions.
    
  logic         i_sclgen_rst_n_tb          	; // new by badr 

// Configurations signals
  logic [7:0]   i_regf_config_tb           	;
  logic         i_data_config_mux_sel_tb   	;  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
  logic [11:0]  i_regf_wr_address_config_tb	;
  logic         i_regf_wr_en_config_tb     	;
  logic         i_regf_rd_en_config_tb     	;

  wire          sda_tb                     	; // sda line
    
  logic         scl_tb                     	; // scl bus
  logic         o_sdr_rx_valid_tb          	; // output to host >> valid data are loaded    //2023
  logic         o_ctrl_done_tb              ; //2023

//-----------------------------Internal signals -------------------------------------//
logic sda_drive;
bit frame_ended;
int cycle_count ;

//-----------------------------Parameters-------------------------------------//
    parameter CLK_PERIOD  = 10;
    parameter configuration   = 1'b1 ;
    parameter Design          = 1'b0 ;
    parameter config_location = 12'd1000 ;

    parameter EXPECTED_BROADCAST = 8'b11111100; // 'h7E+ R/W bit = 0
    parameter EXPECTED_ENTHDR0 = 9'b001000000;
    
    reg [2:0] RAND_CMD_ATTR  = 'd1   ;
    reg [3:0] RAND_TID       = 'd3   ;
    reg [7:0] RAND_CMD       = 8'h00 ;
    reg       RAND_CP        = 1     ;
    reg [4:0] RAND_DEV_INDEX = 'd3   ;
    reg [1:0] RAND_RESERVED  = 'd0   ;
    reg [2:0] RAND_DTT       = 'd1   ;
    reg [2:0] RAND_MODE      = 'd6   ;
    reg       RAND_RnW       = 1'b0  ; // write   
    reg       RAND_WROC      = 1'd0  ;
    reg       RAND_TOC       = 1'b1  ;
    reg [7:0] RAND_DEF_BYTE  = 'd1   ;
    reg [7:0] RAND_DATA_TWO  = 'd2   ;
    reg [7:0] RAND_DATA_THREE= 'd3   ;
    reg [7:0] RAND_DATA_FOUR = 'd4   ;

//----------------------------- Clock Generation-------------------------------------//
always #(CLK_PERIOD/2) i_sdr_clk_tb = ~i_sdr_clk_tb;

//-----------------------------  Initial block  -------------------------------------//
// locally driven value
assign sda_tb   = sda_drive 			;

initial begin

	initialize();
	reset();

	// change mux selector to write configurations
	switch_muxes(configuration);
	write_configurations();

	// change mux selector to give the regfile inputs control to design
	switch_muxes(Design);


			//<-------------------------TEST CASE 1 ----------------------->//
			//<            Mode --> HDR, TOC = 1, CP = 1 (CCC) ,Broadcast CCC :ENEC       >//

	i_i3c_i2c_sel_tb     			        = 1'b1;
    i_controller_en_tb 						= 1'b1;

    check_output(); //temporary to check enthdr ccc output

// first second preamble for data word
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;

// second second preamble for repeated data word
#(CLK_PERIOD)
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b1;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;    

@(posedge o_ctrl_done_tb)
i_controller_en_tb = 1'b0;


			//<-------------------------TEST CASE 2 ----------------------->//
			//<            Mode --> HDR, TOC = 0, CP = 1 (CCC) ,Direct CCC :ENEC       >//

    RAND_CMD       = 8'h80 ;
    RAND_TOC       = 1'b0  ;	
  
  // change mux selector to write configurations
	switch_muxes(configuration);
	write_configurations();

	// change mux selector to give the regfile inputs control to design
	switch_muxes(Design);

	i_i3c_i2c_sel_tb     			        = 1'b1;
    i_controller_en_tb 						= 1'b1;	
    check_output(); //temporary to check enthdr ccc output

    // first second preamble for data word
@(negedge DUT.CCC_Handler.o_rx_en )
	sda_drive = 'b0;
  #(4*CLK_PERIOD)
    sda_drive = 'bz;


//@(DUT.tx.i_ddrccc_tx_mode == 15)
//DUT.CCC_Handler.i_sclstall_stall_done = 1;
  

    #5000
    $stop;
end
pullup(sda_tb);
//-----------------------------     Tasks       -------------------------------------//

task reset;
	begin
	    i_sdr_rst_n_tb 		        = 1'b1;
		# (CLK_PERIOD)
		i_sdr_rst_n_tb 				= 1'b0; // activated
		# (CLK_PERIOD)
		i_sdr_rst_n_tb 				= 1'b1; // de-activated

	end	
	endtask

task initialize; 
	begin
		i_sdr_clk_tb 				= 1'b0;
		i_sdr_rst_n_tb 				= 1'b1;
		i_i3c_i2c_sel_tb        	= 1'b1;  //i3c mode
		i_controller_en_tb      	= 1'b0;
		i_ccc_en_dis_hj_tb      	= 1'b0;
		sda_drive 					= 1'bz;
		i_data_config_mux_sel_tb    = 1'b1;
		i_regf_rd_en_config_tb   	= 1'b0;								
    	i_regf_wr_en_config_tb   	= 1'b1;

	end
	endtask

task switch_muxes(input selector);
        begin 
            i_data_config_mux_sel_tb = selector ; // 1 for configuration and 0 for design 
        end 
    endtask 

task write_configurations();
	begin

//1.write randomized values
	// DWORD0
	 	i_regf_wr_en_config_tb = 1'b1;
	 #(2*CLK_PERIOD)																		    																									; 
		i_regf_config_tb     = { RAND_CMD[0] , RAND_TID , RAND_CMD_ATTR }  												    ;
    	i_regf_wr_address_config_tb = config_location 																												;
    	    
      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_CP , RAND_CMD[7:1] } 															    							;
    	i_regf_wr_address_config_tb = config_location + 'd1 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_DTT[0] , RAND_RESERVED , RAND_DEV_INDEX }  											;		    
    	i_regf_wr_address_config_tb = config_location + 'd2 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { RAND_TOC , RAND_WROC , RAND_RnW ,RAND_MODE , RAND_DTT[2:1]} 		;
    	i_regf_wr_address_config_tb = config_location + 'd3 																									;

      // DWORD 1
       #(2*CLK_PERIOD)  																																									  ; 
		i_regf_config_tb     = RAND_DEF_BYTE     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd4 																									;		

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = RAND_DATA_TWO     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd5 																									;

       #(2*CLK_PERIOD); 																		 
		i_regf_config_tb     = RAND_DATA_THREE     																													;
    	i_regf_wr_address_config_tb  = config_location + 'd6 																									;

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = RAND_DATA_FOUR     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd7 																									;
  
        #(CLK_PERIOD) 																																											;
	end
endtask : write_configurations


task check_output ();
	begin
		logic [7:0] BROADCAST; // 7'h7E+ R/w bit
		logic [8:0] ENTHDR0; 

		BROADCAST = 8'b0; // 7'h7E+ R/w bit
		ENTHDR0 = 9'b0;
		// ddr code: 0x20 + T-bit
		//frame_ended = 1'b0;
		// once you see the start condition--> sample the first data 7E then sample 'h20 then the parity bit
		/*bit start_condition;
		start_condition = ~sda_tb &&  ~scl_tb 
		if(start_condition) begin
			data_check[i] <= //sda
		end
*/ /*
			for(int i=0; i < 8 ; i++)   //receive first 8 bits of 7E and write bit
			 	begin  
				   @(posedge scl_tb)
				   	BROADCAST['d7 - i] = sda_tb;
			 	end

			@(negedge scl_tb)
			if(BROADCAST == EXPECTED_BROADCAST)
			 begin
					$display("Broadcast frame is received");
					send_ack();
			 end

			for(int i=0; i < 9 ; i++)   //receive first 8 bits of 7E and write bit
			 	begin  
				   @(posedge scl_tb)
				   	ENTHDR0['d8 - i] = sda_tb;
			 	end
 

			if(ENTHDR0 == EXPECTED_ENTHDR0) begin
				$display("ENTHDR frame is received");

				@(negedge scl_tb)
				#(CLK_PERIOD)
				frame_ended = 1'b1;
				#(CLK_PERIOD)
				frame_ended = 1'b0;


end	   		
		
	end 
endtask

task send_ack;
	begin
		//#(30*CLK_PERIOD)
		#(2*CLK_PERIOD)
			if(!scl_tb)       //drive ack when scl is low
			  begin  	
					sda_drive = 1'b0; //ack bit

				  @(negedge scl_tb)
				  //#(30*CLK_PERIOD)
				  #(2*CLK_PERIOD)

						if(!scl_tb)
				 			sda_drive = 'bz;     
			  end
	end
endtask



//-----------------------------DUT Instantiation-------------------------------------//
I3C_TOP DUT (
 .i_sdr_clk           		(i_sdr_clk_tb)					, 
 .i_sdr_rst_n         		(i_sdr_rst_n_tb)				, 
 .i_controller_en     		(i_controller_en_tb)			, 
 .i_i3c_i2c_sel       		(i_i3c_i2c_sel_tb)				, 
 .i_ccc_en_dis_hj     		(i_ccc_en_dis_hj_tb)			, 
 .i_regf_config             (i_regf_config_tb)				,
 .i_data_config_mux_sel     (i_data_config_mux_sel_tb)		,    
 .i_regf_wr_address_config  (i_regf_wr_address_config_tb)	,
 .i_regf_wr_en_config       (i_regf_wr_en_config_tb)		,
 .i_regf_rd_en_config       (i_regf_rd_en_config_tb)        ,   
 .sda                 		(sda_tb)						,
 .scl                 		(scl_tb)						,
 .o_sdr_rx_valid      		(o_sdr_rx_valid_tb)				,
 .o_ctrl_done               (o_ctrl_done_tb)
 );

endmodule

// DUT.sys_clk_50mhz ;

    parameter scl_pos_wrt_sys_clc = 4 ;         // used in sdr transmission trancking changes every pos edge only of sda 
    parameter scl_pos_neg_wrt_sys_clc = 2 ;     // used in hdr transmission trancking changes every pos or neg edge of sda 

    //////////////////////////////////////////////////// ENTHDR assertion /////////////////////////////////////
    sequence start_bit_1 ;
        (sda_tb == 1'b1 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_2 ;
        start_bit_1 ##(1) (sda_tb == 1'b0 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_3 ;
        start_bit_2 ##(3) (sda_tb == 1'b0 && scl_tb == 1'b0 ); 
    endsequence

    sequence start_bit_4 ;
        start_bit_3 ##(1) (sda_tb == 1'b1 && scl_tb == 1'b0 ); 
    endsequence

    // end of START condition
    ////////////////////////////////////////////////////////////////////////

    sequence ENTHDR_1 ;                        // first bit of seven E is transmitted above and it's duration is here 
        start_bit_4 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_2 ;                       
        ENTHDR_1 ##(5*scl_pos_wrt_sys_clc) sda_tb == 1'b0 ;
    endsequence

    sequence ENTHDR_3 ;
        ENTHDR_2 ##(4*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_4 ;
        ENTHDR_3 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b0;
    endsequence

    sequence START_ENTHDR_sec;
        ENTHDR_4 ##(6*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ; // this is the first bit in the HDR mode i.e (RnW bit)
    endsequence



    // Property to track SDA line ENTHDR frame >> (8'b11111100 then 9'b001000000) then HDR 
    property START_ENTHDR_sec  ;
        @(posedge (DUT.sys_clk_50mhz)) $rose(i_controller_en_tb) |-> START_ENTHDR_sec ;
    endproperty


    // Assert the property
    assert property(START_ENTHDR_sec)
                            $display("%t START_ENTHDR_sec PASSED ",$time); else
                            $display("%t START_ENTHDR_sec FAILED ",$time);

/*
task ccc_broadcast_driver();
	begin

// for second preamble and read data 
//////////////////////////////////////////////  Broadcast driver /////////////////////////////////
// backup works 100 % el7amdulelah 
// for second preamble and read data 
int cycle_count ;
		 // Simulation logic to create the desired pattern (Broadcast)
	 		
    	for (int i=0 ; i<10000 ; i++) begin
    		#(2*CLK_PERIOD); // One clock cycle delay





//------------------------ for direct driving without looping -------------------------------------//
    		wait(DUT.CCC_Handler.i_engine_en);

    		@(negedge DUT.u_scl_generation.o_scl_neg_edge or  negedge DUT.u_scl_generation.o_scl_pos_edge)
        		// Step 1: Randomize for 38 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    sda_drive = $random();
        		    #(CLK_PERIOD); // One clock cycle delay
        		    cycle_count--;
        		end
        		
/*        		// Step 2: Hold at zero for 7 cycles
        		sda_drive = 0;
        		repeat (7) begin
        		#(CLK_PERIOD); // One clock cycle delay
        		end
        
        		// Step 3: Randomize for 38 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    sda_drive =  $random();
        		   	#(CLK_PERIOD); // One clock cycle delay
       		 		cycle_count--;
        		end
        
        		// Step 4: Hold at one for 4 cycles
        		sda_drive = 1;
        		repeat (4) begin
        		    #(CLK_PERIOD); // One clock cycle delay
        		end
        		
        		// Step 5: Randomize until engine_done is set to 1
				sda_drive = $random();
				#(2*CLK_PERIOD); // One clock cycle delay
				wait (DUT.CCC_Handler.o_engine_done) #(2*CLK_PERIOD);
//-----------------------------------------------------------------------------------------------//






				continue ; 
				  
    	 
    end

	end
endtask : ccc_broadcast_driver */

//-------------------------------------------------------- Drivers for CCC Handler -----------------------------------------------// 
/* i have three differnet type of sequences : 
		1- Broadcast
		2- Direct SET 
		3- Direct GET 
*/		 	 	






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





//------------------------ for direct driving without looping -------------------------------------//
    		wait(i_engine_en_tb);
    		@(negedge scl_neg_edge_tb or  negedge scl_pos_edge_tb)
        		// Step 1: Randomize for 38 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    i_sdahnd_rx_sda_tb = $random();
        		    #(CLK_PERIOD); // One clock cycle delay
        		    cycle_count--;
        		end
        		
        		// Step 2: Hold at zero for 7 cycles
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
//-----------------------------------------------------------------------------------------------//






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





    //------------------------ for direct driving without looping -------------------------------------//
    		wait(i_engine_en_tb);
    		@(negedge scl_neg_edge_tb or  negedge scl_pos_edge_tb)
        		// Step 1: Randomize for 38 cycles
        		cycle_count = 37;
        		while (cycle_count > 0) begin
        		    i_sdahnd_rx_sda_tb = $random();
        		    #(CLK_PERIOD); // One clock cycle delay
        		    cycle_count--;
        		end
        		
        		// Step 2: Hold at zero for 12 cycles
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

//-----------------------------------------------------------------------------------------------//
















				
				continue ;
				  
    	end 
    end
*/


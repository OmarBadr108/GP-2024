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
//-----------------------------Parameters-------------------------------------//
    parameter CLK_PERIOD  = 10;
    parameter configuration   = 1'b1 ;
    parameter Design          = 1'b0 ;
    parameter config_location = 12'd1000 ;

    parameter EXPECTED_BROADCAST = 8'b11111100; // 'h7E+ R/W bit = 0
    parameter EXPECTED_ENTHDR0 = 9'b001000000;
    
    parameter [2:0] RAND_CMD_ATTR  = 'd0   ;
    parameter [3:0] RAND_TID       = 'd3   ;
    parameter [7:0] RAND_CMD       = 8'h00 ;
    parameter       RAND_CP        = 1     ;
    parameter [4:0] RAND_DEV_INDEX = 'd3   ;
    parameter [1:0] RAND_RESERVED  = 'd0   ;
    parameter [2:0] RAND_DTT       = 'd2   ;
    parameter [2:0] RAND_MODE      = 'd6   ;
    parameter       RAND_RnW       = 1'b0  ; // write   
    parameter       RAND_WROC      = 1'd0  ;
    parameter       RAND_TOC       = 1'b1  ;
    parameter [7:0] RAND_DEF_BYTE  = 'd1   ;
    parameter [7:0] RAND_DATA_TWO  = 'd2   ;
    parameter [7:0] RAND_DATA_THREE= 'd3   ;
    parameter [7:0] RAND_DATA_FOUR = 'd4   ;

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
			//<            Mode --> HDR, TOC = 1, CP = 1 (CCC)            >//

	i_i3c_i2c_sel_tb     			        = 1'b1;
    i_controller_en_tb 						= 1'b1;

    check_output(); //temporary to check output


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
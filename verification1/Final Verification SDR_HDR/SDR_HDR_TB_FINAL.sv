`timescale 1ns/1ps

// This Testbench is divided into:
// 1. Testbench signals
// 2. Clock Generation
// 3. Tasks and Covergroups
// 4. Assertions
// 5. Initial block
// 6. DUT instantiation




// package contains all the randomized input values with their constraints
import pkg ::*;

module SDR_HDR_TB_FINAL ();

	//--------------------------------------------- 1.Testbench signals-----------------------------------//
	// Clock and reset signals
    reg          i_clk_tb           								;
    reg          i_rst_n_tb         								;  
    
    // Design Inputs   
    reg          i_controller_en_tb     						;        
    reg          i_i3c_i2c_sel_tb 			  					;
    reg          i_ccc_en_dis_hj_tb		 	  					;

    reg   [7:0]  i_regf_config_tb            				;
    reg          i_data_config_mux_sel_tb    				;  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
    reg   [11:0] i_regf_wr_address_config_tb 				;
    reg          i_regf_wr_en_config_tb      				;
    reg          i_regf_rd_en_config_tb      				;

    reg          i_ccc_done_tb              				; // done signal from CCC block
    reg          i_ddr_mode_done_tb    	    				; // done signal from ddr block

    wire         sda_tb                	   					;

   
    // Design Outputs
    wire         o_sdr_rx_valid_tb     	    				; // output to host >> valid data are loaded
    wire         o_ctrl_done_tb        	    				; // sdr block done signal
    wire         scl_tb                	    				;
    wire         o_ddrmode_enable_tb        				; // enable for the ddr block
    wire         o_ccc_enable_tb            				; // enable for the CCC block
    wire  [11:0] o_regf_address_special_tb  				; // regf special address


//------------------------------------------------Internal Wires----------------------------------------//

    logic               sda_drive             ;
    bit 								frame_ended						;
    logic 							i_tx_exit_restart			;

//------------------------------------------------2.Clock Generetaion----------------------------------------//


initial 
	begin
			i_clk_tb = 'b0;
			while(running == 1)
				#(CLK_PERIOD/2) i_clk_tb = ~i_clk_tb;
	end

//------------------------------------------------3.Tasks and Covergroups-----------------------------------//
    
//create object from the class inside the  package	
 configuration cg;

// create a covergroup
covergroup CovPort();
  
  // 1.checking input values coverage after randomization

  CP3: coverpoint i_data_config_mux_sel_tb {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP4: coverpoint DUT.u_hdr_engine.i_TOC {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP5: coverpoint DUT.u_hdr_engine.i_CP {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

 
 ENGINE_CASES: cross CP4,CP5,CP9 {
 		bins CP0_TOC0 = binsof(CP5.zero)&& binsof(CP4.zero) && binsof(CP9.one);
 		bins CP0_TOC1 = binsof(CP5.zero)&& binsof(CP4.one)  && binsof(CP9.one);
 		bins CP1_TOC0 = binsof(CP5.one) && binsof(CP4.zero) && binsof(CP9.one);
 		bins CP1_TOC1 = binsof(CP5.one) && binsof(CP4.one)  && binsof(CP9.one);
 
    ignore_bins not_important = ENGINE_CASES with (CP9 == 0);
 } 


  
  // 2. checking output coverage

  CP9: coverpoint DUT.u_hdr_engine.i_i3cengine_hdrengine_en {
  	 bins zero  = {0};
  	 bins one   = {1};
  }
endgroup : CovPort

  //create handle from this covergroup
CovPort xyz;


//<<<---------------------------------Tasks---------------------------------------->>>//
//Testbench tasks are: 1.run / 2.reset / 3.initialize / 4.check_output / 5.write_configurations/ 6.send_ack

task run ();
begin
	
	int i;
  for (i =0 ; i < 100; i++) 
   	begin

   		// initial values 
  	  i_ddr_mode_done_tb = 1'b0;
  	  i_ccc_done_tb = 1'b0;
			i_controller_en_tb = 1'b0;
 

//configurations should be written either initially at the start of the transmission 
//or during the process when it sees that the tx mode is currently in restart or exit mode

// put initial value for the mux to be 1 to write configuration in the first loop         
	 			if (i == 1'b0)    
	 				begin
	 					 write_configurations();
	 					 xyz.sample(); 
	 				end
    
// change input values to be ready for normal operations in hdr mode

	 			i_i3c_i2c_sel_tb              = 1'b1;
			  i_controller_en_tb 						= 1'b1;
	 			i_data_config_mux_sel_tb      = 1'b0;

	 
       
              //<---------------------- Checking Output ----------------------------->//
        
  																		// Test Case 1// 
  														//Check that ENTHDR CCC is sent.//


        send_enthdr = i_controller_en_tb && i_i3c_i2c_sel_tb && ~i_data_config_mux_sel_tb ;
        
        if(send_enthdr) begin
        	check_output(); // function that reads the sda line and compares it with the correct CCC
        	#(4*CLK_PERIOD)
        	xyz.sample();


  																		 // Test Case 2//
				   // Normal transaction(CP=0) with exit pattern(TOC=1) after it followed by stop bit.//         

        if(!DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ddr block is enabled and then the engine returns to sdr mode and sends stop bit

        		#(1000*CLK_PERIOD)
        		   //start writing configurations before the ddr block finishes
        		write_configurations();

        		#(100*CLK_PERIOD)


        		i_ddr_mode_done_tb = 1'b1;
        		#(2*CLK_PERIOD)
        		i_ddr_mode_done_tb = 1'b0;

        		@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        		i_controller_en_tb = 1'b0;
        		send_enthdr        = 1'b0;
        		#(20*CLK_PERIOD);
        		xyz.sample();
        		continue;
        	end


      																// Test Case 3//
      						// CCC(CP=1) with exit pattern(TOC=1) after it followed by stop bit.// 

        else if(DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ccc block is enabled and then the engine returns to sdr mode and sends stop bit
        		#(1000*CLK_PERIOD)
        		   //start writing configurations before the ddr block finishes
        		write_configurations();

        		#(100*CLK_PERIOD)


        		i_ccc_done_tb = 1'b1;
        		#(2*CLK_PERIOD)
        		i_ccc_done_tb = 1'b0;

        		@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        		i_controller_en_tb = 1'b0;
        		send_enthdr        = 1'b0;
        		#(20*CLK_PERIOD);
        		xyz.sample();
        		continue;

        	end

       																// Test Case 4//
       				// Normal Transaction(CP=0) with restart pattern(TOC=0) after it block is enabled again.//

        else if(!DUT.u_hdr_engine.i_CP_temp && !DUT.u_hdr_engine.i_TOC_temp && DUT.u_i3c_engine.o_hdrengine_en)
        	begin


        //check that ddr block is enabled and then the engine returns to sdr mode and sends stop bit

        		#(1000*CLK_PERIOD)
        		   //start writing configurations before the ddr block finishes
        		write_configurations();
						        		

        		#(100*CLK_PERIOD)

        		i_ddr_mode_done_tb = 1'b1;
        		#(2*CLK_PERIOD)
        		i_ddr_mode_done_tb = 1'b0;

        		xyz.sample();
        		
        		if(DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp)
        				begin
        	  		
        				#(1000*CLK_PERIOD)
        				   //start writing configurations before the ddr block finishes
        				write_configurations();

        				#(100*CLK_PERIOD)


        				i_ccc_done_tb = 1'b1;
        				#(2*CLK_PERIOD)
        				i_ccc_done_tb = 1'b0;

        				@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        				i_controller_en_tb = 1'b0;
        				send_enthdr        = 1'b0;
        				#(20*CLK_PERIOD);
        				xyz.sample();
        				continue;
        				end
        		

        		else if(!DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp) 
        			begin
        				#(1000*CLK_PERIOD)
        				   //start writing configurations before the ddr block finishes
        				write_configurations();

        				#(100*CLK_PERIOD)


        				i_ddr_mode_done_tb = 1'b1;
        				#(2*CLK_PERIOD)
        				i_ddr_mode_done_tb = 1'b0;

        				@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        		i_controller_en_tb = 1'b0;
        		send_enthdr        = 1'b0;
        		#(20*CLK_PERIOD);
        		xyz.sample();
        			end

        			else begin
        				reset();
        				continue;
        			end

        end
        else if(DUT.u_hdr_engine.i_CP_temp && !DUT.u_hdr_engine.i_TOC_temp && DUT.u_i3c_engine.o_hdrengine_en)
        	begin


        //check that ddr block is enabled and then the engine returns to sdr mode and sends stop bit

        		#(1000*CLK_PERIOD)
        		   //start writing configurations before the ddr block finishes
        		write_configurations();
						        		

        		#(100*CLK_PERIOD)

        		i_ccc_done_tb = 1'b1;
        		#(2*CLK_PERIOD)
        		i_ccc_done_tb = 1'b0;

        		xyz.sample();
        		
        		if(DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp)
        				begin
        	  		
        				#(1000*CLK_PERIOD)
        				   //start writing configurations before the ddr block finishes
        				write_configurations();

        				#(100*CLK_PERIOD)


        				i_ccc_done_tb = 1'b1;
        				#(2*CLK_PERIOD)
        				i_ccc_done_tb = 1'b0;

        				@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        		i_controller_en_tb = 1'b0;
        		send_enthdr        = 1'b0;
        		#(20*CLK_PERIOD);
        		xyz.sample();
        		continue;
        				end
        		

        else if(!DUT.u_hdr_engine.i_CP_temp && DUT.u_hdr_engine.i_TOC_temp) 
        			begin
        				#(1000*CLK_PERIOD)
        				   //start writing configurations before the ddr block finishes
        				write_configurations();

        				#(100*CLK_PERIOD)


        				i_ddr_mode_done_tb = 1'b1;
        				#(2*CLK_PERIOD)
        				i_ddr_mode_done_tb = 1'b0;

        				@(posedge DUT.u_i3c_engine.i_tx_mode_done)  // to check that hdrengine done is enabled and return to sdr mode
        				i_controller_en_tb = 1'b0;
        				send_enthdr        = 1'b0;
        				#(20*CLK_PERIOD);
        				xyz.sample();
        				continue;
        			end

        			else begin
        				reset();
        				continue;
        			end

        		end

        end
          #(CLK_PERIOD);	
        	xyz.sample();

	
      end
     end 
 
	endtask

task write_configurations();
	begin

// 1.randomize
cg = new();
cg.randomize();

//2.write randomized values
	// DWORD0
		i_data_config_mux_sel_tb = 1'b1;
	 	i_regf_wr_en_config_tb = 1'b1;
	 #(2*CLK_PERIOD)																		    																									; 
		i_regf_config_tb     = { cg.RAND_CMD[0] , cg.RAND_TID , cg.RAND_CMD_ATTR }  												    ;
    	i_regf_wr_address_config_tb = config_location 																												;
    	    
      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { cg.RAND_CP , cg.RAND_CMD[7:1] } 															    							;
    	i_regf_wr_address_config_tb = config_location + 'd1 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { cg.RAND_DTT[0] , cg.RAND_RESERVED , cg.RAND_DEV_INDEX }  											;		    
    	i_regf_wr_address_config_tb = config_location + 'd2 																									;

      #(2*CLK_PERIOD)  																																											; 
		i_regf_config_tb     = { cg.RAND_TOC , cg.RAND_WROC , cg.RAND_RnW ,cg.RAND_MODE , cg.RAND_DTT[2:1]} 		;
    	i_regf_wr_address_config_tb = config_location + 'd3 																									;

      // DWORD 1
       #(2*CLK_PERIOD)  																																									  ; 
		i_regf_config_tb     = cg.RAND_DEF_BYTE     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd4 																									;		

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = cg.RAND_DATA_TWO     																														;
    	i_regf_wr_address_config_tb  = config_location + 'd5 																									;

       #(2*CLK_PERIOD); 																		 
		i_regf_config_tb     = cg.RAND_DATA_THREE     																													;
    	i_regf_wr_address_config_tb  = config_location + 'd6 																									;

       #(2*CLK_PERIOD)  																																										; 
		i_regf_config_tb     = cg.RAND_DATA_FOUR     																														;
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
		#(30*CLK_PERIOD)
			if(!scl_tb)       //drive ack when scl is low
			  begin  	
					sda_drive = 1'b0; //ack bit

				  @(negedge scl_tb)
				  #(30*CLK_PERIOD)

						if(!scl_tb)
				 			sda_drive = 'bz;     
			  end
	end
endtask


task reset;
	begin
	   i_rst_n_tb 		      = 1'b1;
		# (CLK_PERIOD)
		i_rst_n_tb 				= 1'b0; // activated
		# (CLK_PERIOD)
		i_rst_n_tb 				= 1'b1; // de-activated

	end	
	endtask

	task initialize; 
	begin
		i_clk_tb 				= 1'b0;
		i_rst_n_tb 				= 1'b1;
		i_i3c_i2c_sel_tb        = 1'b1;  //i3c mode
		i_controller_en_tb      = 1'b0;
		i_ccc_en_dis_hj_tb      = 1'b0;
      i_ccc_done_tb			= 1'b0;
      i_ddr_mode_done_tb      = 1'b0;
		sda_drive 				= 1'bz;
		//i_ddr_pp_od_tb			= 1'b0;
		//i_ddr_pp_od_tb			= 1'b0;
		i_data_config_mux_sel_tb   = 1'b1;
		i_regf_rd_en_config_tb   	= 1'b0;								
    	i_regf_wr_en_config_tb   	= 1'b1;

	end
	endtask

//------------------------------------------------4. Assertions-----------------------------------//

																							//---TEST CASE 1---//
															// ENTHDR DONE FLAG IS HIGH AFTER RECEIVING THE FRAME//	
property p1 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb) 
	 (send_enthdr && frame_ended) |-> ##1 DUT.u_enthdr.o_i3cengine_done 
endproperty
	assert property(p1) $display("ENTHDR DONE FLAG IS HIGH %t",$time); else $error ("error in enthdr flag to engine");
 	cover property(p1);




 																							//---TEST CASE 2---//
 												// HDR ENGINE IS ENABLED AFTER THE ENTHDR DONE FLAG IS HIGH//
property p2 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	 $fell(DUT.u_enthdr.o_i3cengine_done) |-> ##1  DUT.u_i3c_engine.o_hdrengine_en 
endproperty
	assert property(p2);/* $display("HDR ENGINE IS ENABLED %t",$time); else $error ("HDR ENGINE IS NOT ENABLED %t",$time);*/
 	cover property(p2);


 																							//---TEST CASE 3---//
 												             // IF CP = 0(N.T.), DDR BLOCK IS ENABLED//


property p3 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	(!DUT.u_hdr_engine.i_CP && DUT.u_i3c_engine.o_hdrengine_en && !DUT.u_hdr_engine.i_TOC && ~i_data_config_mux_sel_tb) 
	|->  ##2 DUT.u_hdr_engine.o_ddrmode_en
endproperty
	assert property(p3); /* $display("Flags1 are correct %t",$time); else $error("Error in flags1 %t",$time); */
	cover property(p3);


 																							//---TEST CASE 4---//
 												             // IF CP = 1(CCC), CCC BLOCK IS ENABLED//


property p4 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	(DUT.u_hdr_engine.i_CP && DUT.u_i3c_engine.o_hdrengine_en && !DUT.u_hdr_engine.i_TOC && ~i_data_config_mux_sel_tb ) 
	|->  ##2 DUT.u_hdr_engine.o_ccc_en
endproperty
	assert property(p4); /*$display("Flags1 are correct %t",$time); else $error("Error in flags1 %t",$time);*/
	cover property(p4);	


	 																							//---TEST CASE 5---//
 												  // IF CP = 0(N.T.) && TOC=1 (EXIT) && ddr_done = 1--> ENGINE DONE=1 //
 
property p5 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	 ($rose(i_ddr_mode_done_tb) && DUT.u_i3c_engine.o_hdrengine_en && DUT.u_hdr_engine.i_TOC_temp) 
	 |->  ##1 DUT.u_hdr_engine.o_i3cengine_hdrengine_done
endproperty
	assert property(p5) $display("Engine done is enabled"); else $error("Error in engine done flag");
	cover property(p5);
	 																							//---TEST CASE 6---//
 												  // IF CP = 1(CCC) &&TOC=1 (EXIT)&& CCC_done = 1--> ENGINE DONE=1 //
property p6 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	 ($rose(i_ccc_done_tb) && DUT.u_i3c_engine.o_hdrengine_en &&DUT.u_hdr_engine.i_TOC_temp) 
    |->  ##1 DUT.u_hdr_engine.o_i3cengine_hdrengine_done
endproperty
	assert property(p6); //$display("CCC Block is enabled"); else $error("Error in CCC flag");
	cover property(p6); 

 																							//---TEST CASE 7---//
 												  // IF CP = 1(CCC) &&TOC=0 (RESTART)&& ccc_done = 1-->ccc is enabled again //
property p7 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	( DUT.u_hdr_engine.i_CP && DUT.u_i3c_engine.o_hdrengine_en && i_ccc_done_tb && !DUT.u_hdr_engine.i_TOC_temp ) 
	|->  ##2 DUT.u_hdr_engine.o_ccc_en
endproperty
	assert property(p7); //$display("CCC Block is enabled"); else $error("Error in CCC flag");
	cover property(p7); 


//------------------------------------------------Initial Block-----------------------------------//

  
// locally driven value
assign sda_tb   = sda_drive 			;

initial begin
	xyz = new();

	initialize();
	reset();
	run();
	running = 0;
	$display("Coverage = %.2f%%", xyz.get_coverage());
end
pullup(sda_tb);

//------------------------------------------------Design Instantiation-----------------------------------//

//DUT instantiation
sdr_hdr_transition_top DUT (
 .i_sdr_clk           		(i_clk_tb), 
 .i_sdr_rst_n         		(i_rst_n_tb), 
 .i_controller_en     		(i_controller_en_tb), 
 .i_i3c_i2c_sel       		(i_i3c_i2c_sel_tb), 
 .i_ccc_en_dis_hj     		(i_ccc_en_dis_hj_tb), 
 .i_regf_config        (i_regf_config_tb)					,
 .i_data_config_mux_sel     (i_data_config_mux_sel_tb)					,    
 .i_regf_wr_address_config  (i_regf_wr_address_config_tb)					,
 .i_regf_wr_en_config       (i_regf_wr_en_config_tb)					,
 .i_regf_rd_en_config       (i_regf_rd_en_config_tb)                   ,  
 //.i_hdr_en            		(i_hdr_en_tb), 
 .i_ccc_done          		(i_ccc_done_tb),
 .i_ddr_mode_done     		(i_ddr_mode_done_tb),
 .sda                 		(sda_tb),
 .o_ddrmode_enable       	(o_ddrmode_enable_tb),
 .o_ccc_enable            	(o_ccc_enable_tb),
 .o_regf_address_special  	(o_regf_address_special_tb),
 .scl                 		(scl_tb),
 .o_sdr_rx_valid      		(o_sdr_rx_valid_tb),
 .o_ctrl_done               (o_ctrl_done_tb)
 );
 

endmodule
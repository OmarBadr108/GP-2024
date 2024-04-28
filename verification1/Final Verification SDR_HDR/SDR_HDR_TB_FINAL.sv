`timescale 1ns/1ps

// This Testbench is divided into:
// 1. Testbench signals
// 2. Clock Generation
// 3. Tasks and Covergroups
// 4. Assertions
// 5. Initial block
// 6. DUT instantiation



//`include "pkg.sv"
// package contains all the randomized input values with their constraints
import pkg ::*;

module SDR_HDR_TB_FINAL ();

	//--------------------------------------------- 1.Testbench signals-----------------------------------//
	// Clock and reset signals
    reg          i_clk_tb           		;
    reg          i_rst_n_tb         		;  
    
    // Design Inputs   
    reg          i_controller_en_tb     	;        
    reg          i_i3c_i2c_sel_tb 			;
    //reg          i_hdr_en_tb				   ; // enable signal for the hdr mode
    reg          i_ccc_en_dis_hj_tb			;

    reg   [7:0]  i_regf_config_tb            ;
    reg          i_data_config_mux_sel_tb    ;  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
    reg   [11:0] i_regf_wr_address_config_tb ;
    reg          i_regf_wr_en_config_tb      ;
    reg          i_regf_rd_en_config_tb      ;

    reg          i_ccc_done_tb            ; // done signal from CCC block
    reg          i_ddr_mode_done_tb    	; // done signal from ddr block

    wire         sda_tb                		;

   
    // Design Output
    wire         o_sdr_rx_valid_tb     	  ; // output to host >> valid data are loaded
    wire         o_ctrl_done_tb        	  ; // sdr block done signal
    wire         scl_tb                	  ;
    wire         o_ddrmode_enable_tb        ; // enable for the ddr block
    wire         o_ccc_enable_tb            ; // enable for the CCC block
    wire  [11:0] o_regf_address_special_tb  ; // regf special address


//------------------------------------------------Internal Wires----------------------------------------//
    logic               sda_drive             ;
    bit frame_ended;
    event event_a;


//------------------------------------------------2.Clock Generetaion----------------------------------------//

//always #(CLK_PERIOD/2) i_clk_tb = ~i_clk_tb;
initial begin
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
  CP1: coverpoint cg.i_controller_en {
    bins zero = {0};
    bins one =  {1};
  }

  CP2: coverpoint cg.i_i3c_i2c_sel {
    bins zero = {0};
    bins one  = {1};
  }
  CP3: coverpoint i_data_config_mux_sel_tb {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP4: coverpoint cg.RAND_TOC {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP5: coverpoint cg.RAND_CP {
  	 bins zero  = {0};
  	 bins one   = {1};
  }


 EN_I3C_MUX : cross CP1,CP2,CP3 {
   bins write_config = binsof(CP1.one) && binsof(CP2.one) && binsof(CP3.one);   // to ensure that all configurations are written
   bins write_data = binsof(CP1.one) && binsof(CP2.one) && binsof(CP3.zero); // to start writing data instead of configuration
   bins en_i2c = binsof(CP1.one) && binsof(CP2.zero) && binsof(CP3.zero);
   ignore_bins not_important = EN_I3C_MUX with (CP1 == 0); 
 } 

/*
 ENGINE_CASES: cross CP4,CP5,CP9 {
 	 //bins CP0_TOC0_DDR1_CCC0 = binsof(CP4.zero) && binsof(CP5.zero) && binsof(CP7.one) && binsof(CP8.zero);
 	 //bins CP0_TOC0_DDR0_CCC1 = binsof(CP4.zero) && binsof(CP5.zero) && binsof(CP7.zero) && binsof(CP8.one);
//
 	 //bins CP0_TOC1_DDR1_CCC0 = binsof(CP4.zero) && binsof(CP5.one) && binsof(CP7.one) && binsof(CP8.zero);
 	 //bins CP0_TOC1_DDR0_CCC1 = binsof(CP4.zero) && binsof(CP5.one) && binsof(CP7.zero) && binsof(CP8.one);
//
   //bins CP1_TOC0_DDR1_CCC0 = binsof(CP4.one) && binsof(CP5.zero) && binsof(CP7.one) && binsof(CP8.zero);
 	 //bins CP1_TOC0_DDR0_CCC1 = binsof(CP4.one) && binsof(CP5.zero) && binsof(CP7.zero) && binsof(CP8.one);
//
 	 //bins CP1_TOC1_DDR1_CCC0 = binsof(CP4.one) && binsof(CP5.one) && binsof(CP7.one) && binsof(CP8.zero);
   //bins CP1_TOC1_DDR0_CCC1 = binsof(CP4.one) && binsof(CP5.one) && binsof(CP7.zero) && binsof(CP8.one);
 }
 */
 ENGINE_CASES: cross CP3,CP4,CP5,CP9 {
 		bins CP0_TOC0_read = binsof(CP5.zero)&& binsof(CP4.zero) && binsof(CP3.zero) && binsof(CP9.one);
 		bins CP0_TOC1_read = binsof(CP5.zero)&& binsof(CP4.one)  && binsof(CP3.zero) && binsof(CP9.one);
 		bins CP1_TOC0_read = binsof(CP5.one) && binsof(CP4.zero) && binsof(CP3.zero) && binsof(CP9.one);
 		bins CP1_TOC1_read = binsof(CP5.one) && binsof(CP4.one)  && binsof(CP3.zero) && binsof(CP9.one);

 		bins CP0_TOC0_write = binsof(CP5.zero)&& binsof(CP4.zero) && binsof(CP3.one) && binsof(CP9.one);
 		bins CP0_TOC1_write = binsof(CP5.zero)&& binsof(CP4.one)  && binsof(CP3.one) && binsof(CP9.one);
 		bins CP1_TOC0_write = binsof(CP5.one) && binsof(CP4.zero) && binsof(CP3.one) && binsof(CP9.one);
 		bins CP1_TOC1_write = binsof(CP5.one) && binsof(CP4.one)  && binsof(CP3.one) && binsof(CP9.one);
 
    ignore_bins not_important = ENGINE_CASES with (CP9 == 0);
 } 


  
  // 2. checking output coverage
  // 2.1 ENTHDR states coverage check
  /*
  CP6: coverpoint DUT.u_enthdr.state {
    bins  t1 = (IDLE       => BROADCAST);
    bins  t2 = (BROADCAST  => ACK);
    bins  t3 = (ACK        => ENTHDR_DDR);
    bins  t4 = (ENTHDR_DDR => PARITY);
    bins  t5 = (PARITY     => IDLE);
    //bins flow = (IDLE       => BROADCAST => ACK        => ENTHDR_DDR)
  } */ 

  CP7: coverpoint i_ddr_mode_done_tb {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP8: coverpoint i_ccc_done_tb {
  	 bins zero  = {0};
  	 bins one   = {1};
  }

  CP9: coverpoint DUT.u_hdr_engine.i_i3cengine_hdrengine_en {
  	 bins zero  = {0};
  	 bins one   = {1};
  }
endgroup : CovPort

  //create handle from this covergroup
CovPort xyz;

task run ();
begin
	//bit send_enthdr;
	int i;
  for (i =0 ; i < 800; i++) 
   	begin
  	  i_ddr_mode_done_tb = 1'b0;
  	  i_ccc_done_tb = 1'b0;
	 		cg = new();
	 		cg.randomize();
    
                  
	 			if (i == 'b0)    // put initial value for the mux to be 1 to write configuration in the first loop
	 				begin
	 					 cg.i_data_config_mux_sel = 1'b1;
	 					 cg.i_regf_wr_en_config = 1'b1;   	
	 				end
    
    
	     if(cg.i_data_config_mux_sel == 1'b1 && cg.i_regf_wr_en_config) // write configurations if : initially sel = 1 or randomized value of the sel is 1
	 				begin
	 		 				write_configurations();
	 		 				//cg.i_data_config_mux_sel      = 1'b0        ;
	 				end
	 
	 	    i_controller_en_tb            = cg.i_controller_en  			;               
        i_i3c_i2c_sel_tb              = cg.i_i3c_i2c_sel     			;           
        i_data_config_mux_sel_tb      = cg.i_data_config_mux_sel        ;                    
        i_regf_wr_en_config_tb        = cg.i_regf_wr_en_config          ;   
        i_regf_rd_en_config_tb        = cg.i_regf_rd_en_config          ;    
        //i_ccc_done_tb                 = cg.i_ccc_done          			;
        //i_ddr_mode_done_tb            = cg.i_ddr_mode_done     			;
	 
       
              //<---------------------- Checking Output ----------------------------->//
        
  																		// Test Case 1// 
  														//Check that ENTHDR CCC is sent.//


        send_enthdr = i_controller_en_tb && i_i3c_i2c_sel_tb && ~i_data_config_mux_sel_tb ;
        
        if(send_enthdr) begin
        	check_output(); // function that reads the sda line and compares it with the correct CCC


  																		 // Test Case 2//
				   // Normal transaction(CP=0) with exit pattern(TOC=1) after it followed by stop bit.//

        if(!DUT.u_hdr_engine.i_CP && DUT.u_hdr_engine.i_TOC && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ddr block is enabled and then the engine returns to sdr mode and sends stop bit
        		//->event_a;
        		#(100000*CLK_PERIOD)
        		i_ddr_mode_done_tb = 1'b1;


        	end


      																// Test Case 3//
      						// CCC(CP=1) with exit pattern(TOC=1) after it followed by stop bit.//
        if(DUT.u_hdr_engine.i_CP && DUT.u_hdr_engine.i_TOC && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ccc block is enabled and then the engine returns to sdr mode and sends stop bit
        		//->event_a;
        		#(100000*CLK_PERIOD)
        		i_ccc_done_tb = 1'b1;

        	end

       																// Test Case 4//
       				// Normal Transaction(CP=0) with restart pattern(TOC=0) after it block is enabled again.//

        if(!DUT.u_hdr_engine.i_CP && !DUT.u_hdr_engine.i_TOC && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ddr block is enabled and
        		//->event_a;
        		#(100*CLK_PERIOD)
        		i_ddr_mode_done_tb = 1'b1;
        		#(100*CLK_PERIOD)
        		i_ddr_mode_done_tb = 1'b1;
        		//DUT.u_hdr_engine.i_TOC = 1'b1;
        	end

       														// Test Case 5//
       			// CCC(CP=1) with restart pattern(TOC=0) after it block is enabled again.//

        if(DUT.u_hdr_engine.i_CP && !DUT.u_hdr_engine.i_TOC && DUT.u_i3c_engine.o_hdrengine_en)
        	begin
        		//check that ddr block is enabled and
        		//->event_a;
        		#(100000*CLK_PERIOD)
        		i_ccc_done_tb = 1'b1;        		
        		#(100000*CLK_PERIOD)
        		i_ccc_done_tb = 1'b1;
        		//cg.RAND_TOC = 1'b1;
        	end   






        end
                	#(CLK_PERIOD);	
        	xyz.sample();

	
      end


     end
 
	endtask

task write_configurations();
	begin
		     // DWORD0
	 #(2*CLK_PERIOD)																		    			; 
		i_regf_config_tb     = { cg.RAND_CMD[0] , cg.RAND_TID , cg.RAND_CMD_ATTR }  												    ;
    	i_regf_wr_address_config_tb = config_location 															;
    	    
      #(2*CLK_PERIOD)  																		; 
		i_regf_config_tb     = { cg.RAND_CP , cg.RAND_CMD[7:1] } 															    ;
    	i_regf_wr_address_config_tb = config_location + 'd1 														;

      #(2*CLK_PERIOD)  																		; 
		i_regf_config_tb     = { cg.RAND_DTT[0] , cg.RAND_RESERVED , cg.RAND_DEV_INDEX }  											    ;		    
    	i_regf_wr_address_config_tb = config_location + 'd2 														;

      #(2*CLK_PERIOD)  																		; 
		i_regf_config_tb     = { cg.RAND_TOC , cg.RAND_WROC , cg.RAND_RnW ,cg.RAND_MODE , cg.RAND_DTT[2:1]} 										;
    	i_regf_wr_address_config_tb = config_location + 'd3 														;

      // DWORD 1
       #(2*CLK_PERIOD) ;  																		; 
		i_regf_config_tb     = cg.RAND_DEF_BYTE     																;
    	i_regf_wr_address_config_tb  = config_location + 'd4 														;	

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config_tb     = cg.RAND_DATA_TWO     																;
    	i_regf_wr_address_config_tb  = config_location + 'd5 														;

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config_tb     = cg.RAND_DATA_THREE     																;
    	i_regf_wr_address_config_tb  = config_location + 'd6 														;

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config_tb     = cg.RAND_DATA_FOUR     																;
    	i_regf_wr_address_config_tb  = config_location + 'd7 														;
  
        #(CLK_PERIOD) ;
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
 //@(negedge scl_tb)

if(ENTHDR0 == EXPECTED_ENTHDR0) begin
	$display("ENTHDR frame is received");

	@(negedge scl_tb)
	#(CLK_PERIOD)
	frame_ended = 1'b1;
	#(CLK_PERIOD)
	frame_ended = 1'b0;

	//@(frame_ended.triggered);
	//$display($time,"\tEvent triggered");

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
	assert property(p3); /*$display("Flags1 are correct %t",$time); else $error("Error in flags1 %t",$time);*/
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
 												  // IF CP = 0(N.T.) &&TOC=1 (EXIT)&& ddr_done = 1--> ENGINE DONE=1 //
 
property p5 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	 ($rose(i_ddr_mode_done_tb) && DUT.u_i3c_engine.o_hdrengine_en &&DUT.u_hdr_engine.i_TOC && ~i_data_config_mux_sel_tb) 
	 |->  ##1 DUT.u_hdr_engine.o_i3cengine_hdrengine_done
endproperty
	assert property(p5); //$display("CCC Block is enabled"); else $error("Error in CCC flag");
	cover property(p5);
	 																							//---TEST CASE 5---//
/* 												  // IF CP = 1(CCC) &&TOC=1 (EXIT)&& CCC_done = 1--> ENGINE DONE=1 //
property p6 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	 ($rose(i_ccc_done_tb) && DUT.u_i3c_engine.o_hdrengine_en &&DUT.u_hdr_engine.i_TOC) 
    |->  ##1 DUT.u_hdr_engine.o_i3cengine_hdrengine_done
endproperty
	assert property(p6); //$display("CCC Block is enabled"); else $error("Error in CCC flag");
	cover property(p6); 

	 																							//---TEST CASE 6---//
 												  // IF CP = 0(N.T.) &&TOC=0 (RESTART)&& ddr_done = 1-->ddr is enabled again //
property p7 ;
	@(posedge i_clk_tb) disable iff(!i_rst_n_tb)
	( !DUT.u_hdr_engine.i_CP&& DUT.u_i3c_engine.o_hdrengine_en && i_ddr_mode_done_tb&&!DUT.u_hdr_engine.i_TOC) 
	|->  ##2 DUT.u_hdr_engine.o_ddrmode_en
endproperty
	assert property(p7); //$display("CCC Block is enabled"); else $error("Error in CCC flag");
	cover property(p7); */
	 																							//---TEST CASE 7---//
 												  // IF CP = 1(CCC) &&TOC=0 (RESTART)&& ccc_done = 1-->ccc is enabled again //  												    												  												             
/*
property p2 ;
	@(posedge i_clk_tb) frame_ended |->  ##3 DUT.u_enthdr.o_i3cengine_done
endproperty
	assert property(p2) $display("Flags2 are correct"); else $error("Error in flags2");
	cover property(p2);	


 property p3 ;
 	@ (event_a.triggered) DUT.u_hdr_engine.o_ddrmode_en 
 endproperty
 assert property(p3) $display("ddr_en is correct"); else $error("Error in ddr_en");
 

                                                  // Test Case 2//
  assert property (
 	 @(posedge i_clk_tb) (i_ddr_mode_done_tb && cg.i_regf_config_tb) |-> DUT.u_hdr_engine.o_i3cengine_hdrengine_done  
 	 );
*/
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
`timescale 1us / 1ps
`default_nettype none

module SDR_HDR_TB ();

parameter CLK_PERIOD  = 40;

//--------------------------------------------------- Testbench Wires --------------------------------------------//

    // Clock and reset signals
    reg          i_clk_tb           		;
    reg          i_rst_n_tb         		;  
    
    // Design Inputs   
    reg          i_controller_en_tb     	;        
    reg          i_i3c_i2c_sel_tb 			;
    reg          i_hdr_en_tb				; // enable signal for the hdr mode
    reg          i_ccc_en_dis_hj_tb			;
    reg          i_toc_interface_tb    		; // toc : 1 : exit,  0: restart
    reg          i_cp_interface_tb     		; // cp  : 1 : CCC ,  0: normal transaction
    reg  [2:0]   i_MODE_interface_tb   		; // mode = 6 for HDR mode
    reg          i_ccc_done_tb         		; // done signal from CCC block
    reg          i_ddr_mode_done_tb    		; // done signal from ddr block

    wire         sda_tb                		;

   
    // Design Output
    wire         o_sdr_rx_valid_tb     		; // output to host >> valid data are loaded
    wire         o_ctrl_done_tb        		; // sdr block done signal
    wire         scl_tb                		;
    wire         o_ddrmode_enable_tb        ; // enable for the ddr block
    wire         o_ccc_enable_tb            ; // enable for the CCC block
    wire  [7:0]  o_regf_address_special_tb  ; // regf special address


//--------------------------------------------------- Internal Signals --------------------------------------------//
    reg               sda_drive             ;  
    // locally driven value
    assign sda_tb   = sda_drive 			;

    
//--------------------------------------------------- Clock Generation --------------------------------------------//

always #(CLK_PERIOD/2) i_clk_tb = ~i_clk_tb;   


//--------------------------------------------------- Initial Block ------------------------------------------------//
initial begin

//Signals Initialization
	initialize();
	     
//Reset
	reset();        
        
// Test Case: enabling the hdr mode to send the ENTHDR CCC and then enabling the HDR engine     
     
     // INPUTS 
        i_controller_en_tb = 1'b1 ;
        i_i3c_i2c_sel_tb   = 1'b1;
        i_hdr_en_tb        = 1'b1;

        /* @(negedge DUT.u_i3c_engine.i_tx_mode_done)
        if(DUT.u_enthdr.o_tx_mode == 3'b001)
        begin
        	sda_drive   = 'b0;
        	#5000
        	sda_drive   = 'bz;
        end */
        #80100
        sda_drive = 1'b0;
        #10000
        sda_drive = 1'bz;
         #1000000
         $stop ;
         
         
        //#80100
        //sda_drive = 1'b0;
        //#10000
        //sda_drive = 1'bz;
        //#2000
        //sda_tb   = sda_drive



  // #80100

   //$stop ;
end 
pullup(sda_tb);
//--------------------------------------------------- Tasks --------------------------------------------------------//
task initialize; 
	begin
		i_clk_tb 				= 1'b0;
		i_rst_n_tb 				= 1'b1;
		i_i3c_i2c_sel_tb        = 1'b1;  //i3c mode
		i_controller_en_tb      = 1'b0;
		i_hdr_en_tb				= 1'b0;
		i_ccc_en_dis_hj_tb      = 1'b0;
        i_ccc_done_tb			= 1'b0;
        i_ddr_mode_done_tb      = 1'b0;
		sda_drive 				= 1'bz;

	end
	endtask

task reset;
	begin
	    i_rst_n_tb 		        = 1'b1;
		# (CLK_PERIOD)
		i_rst_n_tb 				= 1'b0; // activated
		# (CLK_PERIOD)
		i_rst_n_tb 				= 1'b1; // de-activated

	end	
	endtask

//--------------------------------------------------- Design Instantiation -----------------------------------------//
sdr_hdr_transition_top DUT (
 .i_sdr_clk           		(i_clk_tb), 
 .i_sdr_rst_n         		(i_rst_n_tb), 
 .i_controller_en     		(i_controller_en_tb), 
 .i_i3c_i2c_sel       		(i_i3c_i2c_sel_tb), 
 .i_ccc_en_dis_hj     		(i_ccc_en_dis_hj_tb), 
 .i_toc_interface     		(i_toc_interface_tb),
 .i_cp_interface      		(i_cp_interface_tb),
 .i_MODE_interface    		(i_MODE_interface_tb),  
 .i_hdr_en            		(i_hdr_en_tb), 
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
`default_nettype wire 


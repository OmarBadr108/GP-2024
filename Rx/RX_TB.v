
`timescale 1us/1ps

module RX_SCL_TB ();

// Testbench Wires
reg    			    i_sys_clk_tb            	;
reg    			    i_sys_rst_tb            	;
reg    			    i_ddrccc_rx_en_tb       	;
reg                 i_sdahnd_rx_sda_tb      	;
reg     [4:0]       i_bitcnt_rx_bit_count_tb	;
reg     [3:0]       i_ddrccc_rx_mode_tb     	;
reg                 i_crc_value_tb				;
reg                 i_crc_valid_tb				;
	
wire    [7:0]       o_regfcrc_rx_data_out_tb	;
wire                o_ddrccc_rx_mode_done_tb	;
wire                o_ddrccc_pre_tb				;
wire                o_ddrccc_error_tb			;
wire                o_crc_en_tb        		;         



parameter CLK_PERIOD  = 20;
integer i;

// Internal Wires
wire    			    i_sclgen_scl_tb         	;
wire    			    i_sclgen_scl_pos_edge_tb	;
wire    			    i_sclgen_scl_neg_edge_tb	;

reg					i_sdr_scl_gen_pp_od_tb      ;
reg					i_scl_gen_stall_tb          ;
reg 					i_sdr_ctrl_scl_idle_tb		;
reg 					i_timer_cas_tb				;

wire [7:0] DATA 		= 'b10101101;
wire [7:0] DATA2 		= 'b11001010;

// Clock Generation
 always #(CLK_PERIOD/2) i_sys_clk_tb  = ~ i_sys_clk_tb ;



// Initial Block
initial
	begin
		//----- Signals Initialization------//
		initialize() ;


	    //--------------RESET---------------//
	    reset();


	    //-----------TEST CASE 1 : Normal Transaction >> Read -----------//

	    // 1. Reading ACK bit of the First Data Word

	    i_ddrccc_rx_en_tb   = 1'b1; 
	    i_ddrccc_rx_mode_tb = 4'b0000;  // Preamble state to get the ack bit
	    i_sdahnd_rx_sda_tb  =  'b0;       // driving sda low (ACK)

	    //#(2*CLK_PERIOD)

	    if (o_ddrccc_rx_mode_done_tb )
	    	begin
	     		$display("Preamble is received successfully");
	    	end
	    else 
	    	begin
	    		$display("Preamble is not received correctly");
	    	end
	    
		//#(2*CLK_PERIOD)
	    // 2. Reading First Data Byte

	    i_ddrccc_rx_en_tb   = 1'b1; 
	    i_ddrccc_rx_mode_tb = 4'b0011;   // Deserializing byte mode

	    for (i=1 ; i<9 ; i=i+1) //8 Frames 
       	begin
           @(negedge i_sclgen_scl_tb )
              #10 i_sdahnd_rx_sda_tb = DATA[i-1] ;  
        end
        i_sdahnd_rx_sda_tb = 'bz;



        // 3. Reading Second Data Byte

	    i_ddrccc_rx_en_tb   = 1'b1; 
	    i_ddrccc_rx_mode_tb = 4'b0011;   // Deserializing byte mode

	    for (i=1 ; i<9 ; i=i+1) //8 Frames 
       	begin
           @(negedge i_sclgen_scl_tb )
              #10 i_sdahnd_rx_sda_tb = DATA2[i-1] ;  
        end
        i_sdahnd_rx_sda_tb = 'bz;


        // 4. Checking parity

		i_ddrccc_rx_en_tb   = 1'b1; 
	    i_ddrccc_rx_mode_tb = 4'b0110;   // Check parity state


#1000
$stop;

	end


// Tasks
task initialize; 
	begin
		i_sys_clk_tb 				= 1'b0;
		i_sys_rst_tb 				= 1'b1;
		//i_sclgen_scl_tb             = 1'b0;
		//i_sclgen_scl_pos_edge_tb    = 1'b0;
		//i_sclgen_scl_neg_edge_tb    = 1'b0;
		i_ddrccc_rx_en_tb 			= 1'b0;
		i_sdahnd_rx_sda_tb          = 'bz;
		//i_bitcnt_rx_bit_count_tb    = 'b0;
		//i_ddrccc_rx_mode_tb			=1'b0;
		//i_crc_value_tb				=1'b0;
		i_crc_valid_tb				=1'b0;
		i_scl_gen_stall_tb      = 1'b0;
		i_sdr_ctrl_scl_idle_tb =1'b0;
		i_sdr_scl_gen_pp_od_tb = 1'b1;
		i_timer_cas_tb = 1'b0;
	end
	endtask

task reset;
	begin
		# (CLK_PERIOD)
		i_sys_rst_tb 				= 1'b0; // activated

		# (CLK_PERIOD)
		i_sys_rst_tb 				= 1'b1; // de-activated

		//# (CLK_PERIOD);
	end	
	endtask


// DUT instantiation
RX U0 (
	.i_sys_clk					(i_sys_clk_tb)				,
	.i_sys_rst					(i_sys_rst_tb)				,
	.i_sclgen_scl				(i_sclgen_scl_tb)			,
	.i_sclgen_scl_pos_edge		(i_sclgen_scl_pos_edge_tb)	,
	.i_sclgen_scl_neg_edge		(i_sclgen_scl_neg_edge_tb)	,
	.i_ddrccc_rx_en				(i_ddrccc_rx_en_tb)			,
	.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
	.i_bitcnt_rx_bit_count		(i_bitcnt_rx_bit_count_tb)	,
	.i_ddrccc_rx_mode			(i_ddrccc_rx_mode_tb)		,
	.i_crc_value				(i_crc_value_tb)			,
	.i_crc_valid				(i_crc_valid_tb)			,
			
	.o_regfcrc_rx_data_out		(o_regfcrc_rx_data_out_tb)	,
	.o_ddrccc_rx_mode_done		(o_ddrccc_rx_mode_done_tb)	,
	.o_ddrccc_pre				(o_ddrccc_pre_tb)			,
	.o_ddrccc_error				(o_ddrccc_error_tb)			,
	.o_crc_en					(o_crc_en_tb)                 

);

scl_generation U1 (

    .i_sdr_ctrl_clk     	(i_sys_clk_tb)   							 ,   // 50 MHz clock
    .i_sdr_ctrl_rst_n   	(i_sys_rst_tb)   							 ,
    .i_sdr_scl_gen_pp_od	(i_sdr_scl_gen_pp_od_tb)   					 ,   // 1: Push-Pull      // 0: for Open-Drain
	
    .i_scl_gen_stall    	(i_scl_gen_stall_tb)   						 ,   // 1 for stalling
    .i_sdr_ctrl_scl_idle	(i_sdr_ctrl_scl_idle_tb)   					 ,
    .i_timer_cas        	(i_timer_cas_tb)   							 ,
    	
    .o_scl_pos_edge     	(i_sclgen_scl_pos_edge_tb)   				 ,
    .o_scl_neg_edge     	(i_sclgen_scl_neg_edge_tb)   				 ,
    .o_scl              	(i_sclgen_scl_tb) 
   	
   	);

endmodule
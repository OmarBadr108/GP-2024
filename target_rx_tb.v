module rx_target_tb ();
  
reg    			    i_sys_clk_tb            	;
reg    			    i_sys_rst_tb            	;
reg    			    i_ddrccc_rx_en_tb       	;
reg           i_sdahnd_rx_sda_tb      	;
reg   [3:0]   i_ddrccc_rx_mode_tb;
reg   [4:0]   i_crc_value_tb     ;

reg					i_sdr_scl_gen_pp_od_tb      ;
reg					i_scl_gen_stall_tb          ;
reg 					i_sdr_ctrl_scl_idle_tb		;
reg 					i_timer_cas_tb				;

wire    			    i_sclgen_scl_tb         	;
wire    			    i_sclgen_scl_pos_edge_tb	;
wire    			    i_sclgen_scl_neg_edge_tb	;

wire    [7:0]       o_regfcrc_rx_data_out_tb	;
wire                o_ddrccc_rx_mode_done_tb	;
wire                o_ddrccc_pre_tb				;
wire                o_ddrccc_error_flag_tb			;
wire                o_ddrccc_rnw_tb  ;
wire   [1:0]        o_engine_decision_tb ;
wire   [7:0]        o_ccc_ccc_value_tb  ;
   
integer i;
reg [7:0] data; 
reg [1:0] special_pereamble;  
  
  parameter CLK_PERIOD  = 20;
  always #(CLK_PERIOD/2) i_sys_clk_tb  = ~ i_sys_clk_tb ;
  
  
  target_rx U0 (
	.i_sys_clk					(i_sys_clk_tb)				,
	.i_sys_rst					(i_sys_rst_tb)				,
	.i_sclgen_scl				(i_sclgen_scl_tb)			,
	.i_sclgen_scl_pos_edge		(i_sclgen_scl_pos_edge_tb)	,
	.i_sclgen_scl_neg_edge		(i_sclgen_scl_neg_edge_tb)	,
	.i_ddrccc_rx_en				(i_ddrccc_rx_en_tb)			,
	.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
	.i_ddrccc_rx_mode			(i_ddrccc_rx_mode_tb)		,
	.i_crc_value (i_crc_value_tb),
			
	.o_regfcrc_rx_data_out		(o_regfcrc_rx_data_out_tb)	,
	.o_ddrccc_rx_mode_done		(o_ddrccc_rx_mode_done_tb)	,
	.o_ddrccc_pre				(o_ddrccc_pre_tb)			,
	.o_ddrccc_error_flag				(o_ddrccc_error_flag_tb)			,
	.o_ddrccc_rnw   (o_ddrccc_rnw_tb)  ,
	.o_engine_decision (o_engine_decision_tb) ,
	.o_ccc_ccc_value (o_ccc_ccc_value_tb)      
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

localparam [3:0]  initializing = 'b0000,   //done 
                  pereamble = 'b0001, //done
				          deserializing_data = 'b0010, //done
				          deserializing_ccc_value = 'b0011, //done
				          check_Parity = 'b0100,
				          token_CRC = 'b0101, //done
				          CRC_value = 'b0110, //done
				          deserializing_address = 'b0111, //done
				          deserializing_zeros = 'b1000; //done

task serializing_on_sda;
 input [7:0] to_be_serialized;
 begin
   		for (i = 7 ; i > 0 ; i = i - 1)
		 begin : loop
		   i_sdahnd_rx_sda_tb = to_be_serialized[i];
		   #(2*CLK_PERIOD);
		 end
 end
endtask
 				          

initial 
 begin
   
    i_sys_clk_tb = 0;
		i_sys_rst_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_scl_gen_pp_od_tb = 1;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		
		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b1 ; // not asserted
		
		#((5.5)*CLK_PERIOD);
		
		i_ddrccc_rx_en_tb <= #(CLK_PERIOD/2) 1;
		i_ddrccc_rx_mode_tb <= #(CLK_PERIOD/2) initializing;
		special_pereamble = 2'b01;
		for (i = 1 ; i >= 0 ; i = i - 1)
		 begin 
		   i_sdahnd_rx_sda_tb = special_pereamble[i];
		   #(2*CLK_PERIOD);
		 end 
		data = 8'b10000000;
    serializing_on_sda (data);
    i_sdahnd_rx_sda_tb = data[0];
    #(2*CLK_PERIOD);
    data = 8'b11111101;
    serializing_on_sda (data);
    i_sdahnd_rx_sda_tb = data[0]; 
    #(2*CLK_PERIOD);
		i_sdahnd_rx_sda_tb = 0;
    #(2*CLK_PERIOD);
    i_sdahnd_rx_sda_tb = 1; 
		@(posedge o_ddrccc_rx_mode_done_tb); 
		#(0.5*CLK_PERIOD);	
		if (o_engine_decision_tb != 2'b10)
		  $display ("initializing error"); //end of initialization
		
		
		#(0.5*CLK_PERIOD);		
		i_ddrccc_rx_en_tb <= #(CLK_PERIOD/2) 1;
		i_ddrccc_rx_mode_tb <= #(CLK_PERIOD/2) pereamble;
    i_sdahnd_rx_sda_tb = 1;
		@(posedge o_ddrccc_rx_mode_done_tb)
				if (o_ddrccc_pre_tb != 1)
		  $display ("pereamble error"); //pereamble
		
		  
		#(2*CLK_PERIOD);
		i_ddrccc_rx_en_tb <= 0;
		
		
		#(CLK_PERIOD);
		i_ddrccc_rx_en_tb <= #(CLK_PERIOD/2) 1;
		i_ddrccc_rx_mode_tb <= #(CLK_PERIOD/2) deserializing_data;
		data = 8'b10100101;
    serializing_on_sda (data);
    i_sdahnd_rx_sda_tb = data[0];  
		@(posedge o_ddrccc_rx_mode_done_tb);
		if ((o_regfcrc_rx_data_out_tb != data) | (U0.D1 != data) | (U0.first_byte_full != 1))
		  $display ("data1 error"); //end of data1
		  
		
		#(CLK_PERIOD)
		i_ddrccc_rx_en_tb <= #(CLK_PERIOD/2) 1;
		i_ddrccc_rx_mode_tb <= #(CLK_PERIOD/2) deserializing_data;
		data = 8'b10111101;
    serializing_on_sda (data);
    i_sdahnd_rx_sda_tb = data[0];  
		@(posedge o_ddrccc_rx_mode_done_tb);
		if ((o_regfcrc_rx_data_out_tb != data) | (U0.D2 != data) | (U0.first_byte_full != 0))
		  $display ("data2 error"); //end of data2
		  

		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) check_Parity;
		data = 2'b10;
		for (i = 1 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_error_flag_tb != 0)
		  $display ("parity error"); //end of parity
		
		
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) pereamble;
		#(CLK_PERIOD);
		i_sdahnd_rx_sda_tb = 0;
		#(CLK_PERIOD); 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_pre_tb != 0)
		  $display ("pereamble2 error"); //end of preamble2
		  
	  #(2*CLK_PERIOD);
		i_ddrccc_rx_en_tb <= 0;
		
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) token_CRC;
		data = 4'b1100;
		for (i = 3 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_error_flag_tb != 0)
		  $display ("token error"); //end of token
		  
		i_crc_value_tb = 5'b11100;
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) CRC_value;
		data = 5'b11100;
		for (i = 4 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_error_flag_tb != 0)
		  $display ("crc error"); //end of CRC
		  
		
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) pereamble;
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = 1;
		   #(CLK_PERIOD);
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_pre_tb != 1)
		  $display ("pereamble error"); //end of pereamble act as rd_n_wr bit
	
		
		
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) deserializing_zeros;
		data = 7'b0;
		for (i = 6 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb); //end of zeros
		
		
		
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) deserializing_address;
		data = {7'h66,1'b1};
		for (i = 7 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_error_flag_tb != 0)
		  $display ("address error"); //end of address
		  
		
		
		i_ddrccc_rx_en_tb <= #(1.5*CLK_PERIOD) 1;
		i_ddrccc_rx_mode_tb <= #(1.5*CLK_PERIOD) check_Parity;
		data = 2'b10;
		for (i = 1 ; i >= 0 ; i = i - 1)
		 begin 
		   #(CLK_PERIOD);
		   i_sdahnd_rx_sda_tb = data[i];
		   #(CLK_PERIOD);
		 end 
		@(posedge o_ddrccc_rx_mode_done_tb);
		if (o_ddrccc_error_flag_tb != 0)
		  $display ("CMD_Parity error"); //end of CMD_Parity	
		  
		#(3*CLK_PERIOD);
		
		$stop;
		
		
 end
   	
 endmodule  	

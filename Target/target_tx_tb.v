module tx_tgt_tb();

reg         i_sys_clk_tb;
reg         i_sys_rst_tb;
 
reg         i_ddrccc_tx_en_tb;
reg         i_sdr_scl_gen_pp_od_tb;
 
wire        i_sclgen_scl_tb;
wire        i_sclgen_scl_pos_edge_tb;
wire        i_sclgen_scl_neg_edge_tb;
 
reg [2:0]   i_ddrccc_tx_mode_tb;
reg [7:0]   i_regf_tx_parallel_data_tb;
reg [4:0]   i_crc_crc_value_tb;

wire        o_sdahnd_tgt_serial_data_tb;
wire        o_ddrccc_tx_mode_done_tb;
wire        o_crc_en_tb;
wire [7:0]  o_crc_parallel_data_tb;

reg         i_scl_gen_stall_tb;  
reg         i_sdr_ctrl_scl_idle_tb;
reg         i_timer_cas_tb;


////////////////////CLK////////////////////////////
parameter CLK_PERIOD = 20;
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;
///////////////////////////////////////////////////



localparam    [2:0]     
                          PREAMBLE_ZERO           = 3'b000  , 
 
                          PREAMBLE_ONE            = 3'b001  , 
                          SERIALIZING_BYTE        = 3'b011  , 
    
                          CRC_TOKEN               = 3'b010  ,
    
                          PAR_VALUE               = 3'b110  ,
    
                          CRC_VALUE               = 3'b111  ;
                     


initial
 begin
 
 initialize();
 reset();

  //--------------------------------------TEST CASE 1 : Normal Transaction >> nack ----------------------------------//
  #(6*CLK_PERIOD);
    @(posedge i_sys_clk_tb)
  i_ddrccc_tx_en_tb = 1;
  i_ddrccc_tx_mode_tb = PREAMBLE_ONE;
  
   //--------------------------------------TEST CASE 2 : Normal Transaction >> nack ----------------------------------//
 #(2*CLK_PERIOD);
  @(negedge o_ddrccc_tx_mode_done_tb)
	    i_ddrccc_tx_en_tb   = 1'b1; 
	    i_ddrccc_tx_mode_tb = PREAMBLE_ZERO;
  //--------------------------------------TEST CASE 3 : Normal Transaction >> byte1 ----------------------------------//
 @(negedge o_ddrccc_tx_mode_done_tb)
	    i_regf_tx_parallel_data_tb = 8'b10000101;
	    i_ddrccc_tx_en_tb   = 1'b1; 
	    i_ddrccc_tx_mode_tb = SERIALIZING_BYTE;
//--------------------------------------TEST CASE 4 : Normal Transaction >> byte2 ----------------------------------//
@(negedge o_ddrccc_tx_mode_done_tb)
	    i_regf_tx_parallel_data_tb = 8'b00101011;
	    i_ddrccc_tx_en_tb   = 1'b1; 
	    i_ddrccc_tx_mode_tb = SERIALIZING_BYTE;

//--------------------------------------TEST CASE 5 : Normal Transaction >> par_calc ----------------------------------//

@(negedge o_ddrccc_tx_mode_done_tb)

	    i_ddrccc_tx_en_tb   = 1'b1; 
	    i_ddrccc_tx_mode_tb = PAR_VALUE;


//--------------------------------------TEST CASE 6 : Normal Transaction >> preamble1 ----------------------------------//
  #(6*CLK_PERIOD);
    @(posedge i_sys_clk_tb)
  i_ddrccc_tx_en_tb = 1;
  i_ddrccc_tx_mode_tb = PREAMBLE_ZERO;
  
   //--------------------------------------TEST CASE 2 : Normal Transaction >> preamble0 ----------------------------------//
 #(2*CLK_PERIOD);
  @(negedge o_ddrccc_tx_mode_done_tb)
	    i_ddrccc_tx_en_tb   = 1'b1; 
	    i_ddrccc_tx_mode_tb = PREAMBLE_ONE;




 #(9*CLK_PERIOD);
 $stop ;

	
 end






task initialize; 
	begin
		i_sys_clk_tb 				= 1'b0;
		i_sys_rst_tb 				= 1'b1;
		i_ddrccc_tx_en_tb 	        = 1'b0;

		i_scl_gen_stall_tb      = 1'b0;
		i_sdr_ctrl_scl_idle_tb  = 1'b0;
		i_sdr_scl_gen_pp_od_tb  = 1'b1;
		i_timer_cas_tb          = 1'b0;
	end
	endtask

task reset;
	begin
		# (CLK_PERIOD)
		i_sys_rst_tb 				= 1'b0; // activated

		# (CLK_PERIOD)
		i_sys_rst_tb 				= 1'b1; // de-activated

	end	
	endtask







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

tx_t  U0(
   .i_sys_clk(i_sys_clk_tb),
   .i_sys_rst(i_sys_rst_tb),
   .i_sclgen_scl(i_sclgen_scl_tb),
   .i_sclgen_scl_pos_edge(i_sclgen_scl_pos_edge_tb),
   .i_sclgen_scl_neg_edge(i_sclgen_scl_neg_edge_tb),
   .i_ddrccc_tx_en(i_ddrccc_tx_en_tb),
   .i_ddrccc_tx_mode(i_ddrccc_tx_mode_tb),
   .i_regf_tx_parallel_data(i_regf_tx_parallel_data_tb),
   .i_crc_crc_value(i_crc_crc_value_tb),
   .o_sdahnd_tgt_serial_data(o_sdahnd_tgt_serial_data_tb),
   .o_ddrccc_tx_mode_done(o_ddrccc_tx_mode_done_tb),
   .o_crc_en(o_crc_en_tb), 
   .o_crc_parallel_data(o_crc_parallel_data_tb)
   );









endmodule














module nt_target_tb ();
  /////////nt_target/////////////
  reg i_sys_clk_tb = 1'b0;
  reg i_sys_rst_tb, i_engine_en_tb;
  reg o_cccnt_last_frame_tb;
  wire tx_mode_done_tb, o_ddrccc_rx_mode_done_tb, o_ddrccc_pre_tb;
  wire i_rx_ddrccc_rnw_tb, o_ddrccc_error_tb, o_tx_en_tb, o_nt_rx_en_tb;
  wire [3:0] o_nt_rx_mode_tb;
  wire [2:0] o_tx_mode_tb;
  wire [9:0] o_regf_addr_tb;
  wire o_frmcnt_en_tb, i_sdr_scl_gen_pp_od_tb;
  wire o_engine_done_tb, o_bitcnt_rst_tb, o_bitcnt_en_tb;

nt_target DUT0 (
    .i_sys_clk(i_sys_clk_tb),
    .i_sys_rst(i_sys_rst_tb),
    .i_engine_en(i_engine_en_tb),
    .i_frmcnt_last(o_cccnt_last_frame_tb),
    .i_tx_mode_done(tx_mode_done_tb),
    .i_rx_mode_done(o_ddrccc_rx_mode_done_tb),
    .i_rx_pre(o_ddrccc_pre_tb),
    .i_rx_ddrccc_rnw(i_rx_ddrccc_rnw_tb),
    .i_rx_error(o_ddrccc_error_tb), 
    .o_tx_en(o_tx_en_tb),
    .o_tx_mode(o_tx_mode_tb),
    .o_rx_en(o_nt_rx_en_tb),
    .o_rx_mode(o_nt_rx_mode_tb),
    .o_frmcnt_en(o_frmcnt_en_tb),
    .o_sdahand_pp_od(i_sdr_scl_gen_pp_od_tb),
    .o_regf_wr_en(o_regf_wr_en_tb),
    .o_regf_rd_en(o_regf_rd_en_tb),
    .o_regf_addr(o_regf_addr_tb),
    .o_engine_done(o_engine_done_tb),
    .o_bitcnt_en (o_bitcnt_en_tb),
    .o_bitcnt_rst (o_bitcnt_rst_tb) 
	);
	
	///////////////////////frame_counter//////////////////
/*	reg i_regf_cmd_attr_tb = 1'b0;
	reg i_Direct_Broadcast_n_tb = 1'b1; 
	reg [15:0] i_regf_DATA_LEN_tb = 'd5;
	reg [2:0]  i_regf_DTT_tb;
	wire [5:0]  o_bitcnt_tb;
	wire i_bitcnt_toggle_tb;
		
frame_counter DUT1 (
    .i_fcnt_clk          (i_sys_clk_tb),
    .i_fcnt_rst_n        (i_sys_rst_tb),
    .i_fcnt_en           (o_frmcnt_en_tb),
    .i_regf_CMD_ATTR     (i_regf_cmd_attr_tb),
    .i_regf_DATA_LEN     (i_regf_DATA_LEN_tb),
    .i_regf_DTT          (i_regf_DTT_tb),
    .i_cnt_bit_count     (o_bitcnt_tb),
    .i_bitcnt_toggle     (i_bitcnt_toggle_tb),
    .i_ccc_Direct_Broadcast_n  (i_Direct_Broadcast_n_tb),
    .o_cccnt_last_frame  (o_cccnt_last_frame_tb)
); */

//////////bit_counter////////////////////////
/* wire scl_pos_edge_tb, scl_neg_edge_tb, o_bitcnt_err_rst_tb, o_frcnt_toggle_tb;
 wire [5:0] o_cnt_bit_count_tb;
  
bits_counter DUT2 (
		.i_sys_clk       (i_sys_clk_tb),
		.i_rst_n 	     (i_rst_n_tb),
		.i_bitcnt_en     (o_bitcnt_en_tb),
		.i_scl_pos_edge  (scl_pos_edge_tb),
		.i_scl_neg_edge  (scl_neg_edge_tb),
		.i_cccnt_err_rst (o_bitcnt_err_rst_tb),
		.o_frcnt_toggle (o_frcnt_toggle_tb),
		.o_cnt_bit_count (o_cnt_bit_count_tb)
		
	); */
	
	/////////////////////scl////////////////
	reg i_scl_gen_stall_tb, i_timer_cas_tb, i_sdr_ctrl_scl_idle_tb;
	wire i_sclgen_scl_tb;
	
scl_generation DUT3 (
    .i_sdr_ctrl_clk     	(i_sys_clk_tb),
    .i_sdr_ctrl_rst_n   	(i_sys_rst_tb),
    .i_sdr_scl_gen_pp_od	(i_sdr_scl_gen_pp_od_tb), 	
    .i_scl_gen_stall    	(i_scl_gen_stall_tb),   
    .i_sdr_ctrl_scl_idle	(i_sdr_ctrl_scl_idle_tb),
    .i_timer_cas        	(i_timer_cas_tb), 	
    .o_scl_pos_edge     	(i_sclgen_scl_pos_edge_tb),
    .o_scl_neg_edge     	(i_sclgen_scl_neg_edge_tb),
    .o_scl              	(i_sclgen_scl_tb)                         	
);

/////////////////////rx///////////////////////
reg i_sdahnd_rx_sda_tb;
reg [4:0] i_crc_value_tb = 5'b11010;
wire [7:0] o_regfcrc_rx_data_out_tb, o_ccc_ccc_value_tb;
wire [1:0] o_engine_decision_tb;
wire [3:0]  o_rx_mode_tb;
target_rx DUT4 (
	.i_sys_clk					(i_sys_clk_tb)				,
	.i_sys_rst					(i_sys_rst_tb)				,
	.i_sclgen_scl				(i_sclgen_scl_tb)			,
	.i_sclgen_scl_pos_edge		(i_sclgen_scl_pos_edge_tb)	,
	.i_sclgen_scl_neg_edge		(i_sclgen_scl_neg_edge_tb)	,
	.i_ddrccc_rx_en				(o_rx_en_tb)			,
	.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
	.i_ddrccc_rx_mode			(o_rx_mode_tb)		,
	.i_crc_value (i_crc_value_tb),		
	.o_regfcrc_rx_data_out		(o_regfcrc_rx_data_out_tb)	,
	.o_ddrccc_rx_mode_done		(o_ddrccc_rx_mode_done_tb)	,
	.o_ddrccc_pre				(o_ddrccc_pre_tb)			,
	.o_ddrccc_error_flag				(o_ddrccc_error_tb)			,
	.o_ddrccc_rnw   (i_rx_ddrccc_rnw_tb)  ,
	.o_engine_decision (o_engine_decision_tb) ,
	.o_ccc_ccc_value (o_ccc_ccc_value_tb)      
);

/////////////////tx//////////////////////
reg [7:0] i_regf_tx_parallel_data_tb ;
wire o_sdahnd_tgt_serial_data_tb, o_crc_en_tb;
wire [7:0] o_crc_parallel_data_tb;

tx_t  DUT5(
   .i_sys_clk(i_sys_clk_tb),
   .i_sys_rst(i_sys_rst_tb),
   .i_sclgen_scl(i_sclgen_scl_tb),
   .i_sclgen_scl_pos_edge(i_sclgen_scl_pos_edge_tb),
   .i_sclgen_scl_neg_edge(i_sclgen_scl_neg_edge_tb),
   .i_ddrccc_tx_en(o_tx_en_tb),
   .i_ddrccc_tx_mode(o_tx_mode_tb),
   .i_regf_tx_parallel_data(i_regf_tx_parallel_data_tb),
   .i_crc_crc_value(i_crc_value_tb),
   .o_sdahnd_tgt_serial_data(o_sdahnd_tgt_serial_data_tb),
   .o_ddrccc_tx_mode_done(tx_mode_done_tb),
   .o_crc_en(o_crc_en_tb), 
   .o_crc_parallel_data(o_crc_parallel_data_tb)
);

///////////////////engine_nt_mux////////////////////////
module mux #(parameter n = 1)(
  input [n-1:0] x, y, 
  input s,
  output [n-1:0] z
  );
  assign z = s? x : y;
endmodule

reg engine_en_tb = 1'b1;
reg engine_or_nt;
mux DUT6 (
.x(engine_en_tb),
.y(o_nt_rx_en_tb),
.s(engine_or_nt),
.z(o_rx_en_tb)
);

reg [3:0] engine_mode = 4'b0000;
mux #(4) DUT7 (
.x(engine_mode),
.y(o_nt_rx_mode_tb),
.s(engine_or_nt),
.z(o_rx_mode_tb)
);


////////////////////////////////////////////////////

parameter CLK_PERIOD = 10; 	 	 
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;

integer i;
reg [19:0] data ;
initial 
 begin
  /////////////initializing////////////////
  i_sys_rst_tb = 1'b0;
 	#(CLK_PERIOD);
	i_sys_rst_tb = 1; 
	i_regf_tx_parallel_data_tb = 8'b10110010;
  i_scl_gen_stall_tb = 0;  
  i_sdr_ctrl_scl_idle_tb =0;
  i_timer_cas_tb = 0; 
  #(3.5*CLK_PERIOD);
  engine_or_nt <= #(CLK_PERIOD/2) 1;
  data = {2'b01,1'b1,7'd0,7'h66,1'b1,2'b10}; //testing complete read sequence
  for (i = 0 ; i < 19 ; i = i + 1)
   begin
     i_sdahnd_rx_sda_tb = data[19-i];
     #(2*CLK_PERIOD);
   end
  i_sdahnd_rx_sda_tb = data[0];
  @(o_ddrccc_rx_mode_done_tb);
  if(o_engine_decision_tb == 2'b01)
   begin
    #(CLK_PERIOD); 
    engine_or_nt <= 0;
    i_engine_en_tb <= 1;
   end
  //i_sdahnd_rx_sda_tb = 0; was for testing a framing error case
  i_sdahnd_rx_sda_tb = 1; 
  ////////////////////////////////////////
  @((o_tx_mode_tb == 1) && (tx_mode_done_tb));
  #(2*CLK_PERIOD);
  /*i_sdahnd_rx_sda_tb = 0;
  @(o_engine_done_tb)
  #(CLK_PERIOD);
  i_engine_en_tb <= 0; */ //was for testing aborting case
  i_sdahnd_rx_sda_tb = 1;
  #(2*CLK_PERIOD);
  i_regf_tx_parallel_data_tb = 8'b00110110;
  @(tx_mode_done_tb)
  #(CLK_PERIOD);
  i_regf_tx_parallel_data_tb = 8'b10010010;
  o_cccnt_last_frame_tb = 1;
  @(o_engine_done_tb);
  #(CLK_PERIOD);
  i_engine_en_tb <= 0; //end of full reading sequence ;) 
  #(11*CLK_PERIOD);
  //////////////////////////////////////////
  engine_or_nt <= #(CLK_PERIOD) 1;
  data = {2'b01,1'b0,7'd0,7'h66,1'b0,2'b01}; //testing complete write sequence
  for (i = 0 ; i < 19 ; i = i + 1)
   begin
     i_sdahnd_rx_sda_tb = data[19-i];
     #(2*CLK_PERIOD);
   end
  i_sdahnd_rx_sda_tb = data[0];
  #(CLK_PERIOD);
  engine_or_nt <= 0;
  i_engine_en_tb <= 1;
  #(CLK_PERIOD);
  i_sdahnd_rx_sda_tb = 1; 
  @(tx_mode_done_tb);
  #(2*CLK_PERIOD);
  data[17:0] = {8'b01010101,8'b11001100,2'b11};
  for (i = 0 ; i < 17 ; i = i + 1)
   begin
     i_sdahnd_rx_sda_tb = data[17-i];
     #(2*CLK_PERIOD);
   end  
  /*@(o_engine_done_tb);
  #(CLK_PERIOD);
  i_engine_en_tb <= 0; //it was for testing aborting writing case
  #(5*CLK_PERIOD); */
  data[10:0] = {2'b01,4'b1100,5'b11011};
  for (i = 0 ; i < 10 ; i = i + 1)
   begin
     i_sdahnd_rx_sda_tb = data[10-i];
     #(2*CLK_PERIOD);
   end
  @(o_engine_done_tb && o_ddrccc_error_tb);
  #(CLK_PERIOD);
  i_engine_en_tb <= 0; //complete writing sequence with error in last stage (CRC) to make sure togglig of error flag
  #(5*CLK_PERIOD); 
  $stop;
 end
   
	
endmodule

module top (
//-----------------ddr-----------//
input       	 i_sys_clk,
input       	 i_sys_rst,
input       	 i_engine_en,

input       	 i_regf_toc,          	
input [4:0] 	 i_regf_dev_index,   	
input       	 i_regf_short_read,  	
input       	 i_regf_wroc ,       	
input       	 i_regf_wr_rd_bit,   	
input          	 i_regf_cmd_attr,     	
input [2:0] 	 i_regf_dtt,
			

output           o_regf_wr_en,
output           o_regf_rd_en,
output  [9:0]    o_regf_addr,
output           o_engine_done,
output           o_regf_abort,
output  [3:0]    o_regf_error_type,

//------------tx-----------------//
input [7:0]  	 i_regf_tx_parallel_data,
input [4:0] 	 i_crc_crc_value,

output         	 o_crc_en,
output[7:0] 	 o_crc_parallel_data,
output           o_sdahnd_serial_data,

//-------------rx---------------//
input            i_sdahnd_rx_sda,
input 			 i_crc_valid,         // not exist in tx
output           o_crc_data_valid,    // not exist in tx
output  [7:0]    o_regfcrc_rx_data_out,


//-------------scl---------------//
input 			 i_sdr_ctrl_scl_idle, // to be 0
input            i_timer_cas, // to be 0
output           o_scl,


//-------------frm_cnt---------------//
input 			 i_ccc_Direct_Broadcast_n,
input [15:0]     i_regf_DATA_LEN


);


//-------------------rx wires  --------------------//
wire rx_pre ,rx_error,rx_mode_done,rx_en;
wire [3:0] rx_mode;

//-------------------tx wires  --------------------//
wire tx_mode_done,tx_en;
wire [3:0] tx_mode;
wire [6:0] tx_special_data;

//---------------------bit_cnt wires -------------------------------//
wire bitcnt_en,bitcnt_rst;
wire [5:0] cnt_bit_count;

//---------------------frm_cnt wires -------------------------------//
wire frmcnt_last,frmcnt_en,frcnt_toggle;

//---------------------scl wires -------------------------------//
wire sdahand_pp_od,scl_pos_edge,scl_neg_edge;

//---------------------staller wires -------------------------------//
wire [4:0] sclstall_no_of_cycles;
wire scl_stall,sclstall_en,stall_done;


ddr_mode dut0 (
    .i_sys_clk(i_sys_clk),
    .i_sys_rst(i_sys_rst),
    .i_engine_en(i_engine_en),
	.i_regf_toc(i_regf_toc),
    .i_regf_dev_index(i_regf_dev_index),
    .i_regf_short_read(i_regf_short_read),
    .i_regf_wroc(i_regf_wroc),
    .i_regf_wr_rd_bit(i_regf_wr_rd_bit),
    .i_regf_cmd_attr(i_regf_cmd_attr),
    .i_regf_dtt(i_regf_dtt),


    .i_tx_mode_done(tx_mode_done),
	.o_tx_en(tx_en),
    .o_tx_mode(tx_mode),
	.o_tx_special_data(tx_special_data),
   
    .i_rx_mode_done(rx_mode_done),   
    .i_rx_pre(rx_pre),
    .i_rx_error(rx_error),
	.o_rx_en(rx_en),
    .o_rx_mode(rx_mode),
   
    .i_frmcnt_last(frmcnt_last),
    .o_frmcnt_en(frmcnt_en),
    
	.i_bitcnt(cnt_bit_count),
	.o_bitcnt_en(bitcnt_en),
    .o_bitcnt_rst(bitcnt_rst),
  
    .o_sdahand_pp_od(sdahand_pp_od),
   
	.i_staller_done(stall_done),
	.o_sclstall_no_of_cycles(sclstall_no_of_cycles),  
    .o_sclstall_en(sclstall_en),
    
	
   
    .o_regf_abort(o_regf_abort),
    .o_regf_error_type(o_regf_error_type),	
	.o_regf_wr_en(o_regf_wr_en),
    .o_regf_rd_en(o_regf_rd_en),
	.o_regf_addr(o_regf_addr),
	.o_engine_done(o_engine_done)
	
	
);
tx dut1 (
	.i_sys_clk(i_sys_clk),
    .i_sys_rst(i_sys_rst),
	.i_regf_tx_parallel_data(i_regf_tx_parallel_data),
   
	.i_ddrccc_tx_en(tx_en),
	.i_ddrccc_tx_mode(tx_mode),
    .i_ddrccc_special_data(tx_special_data),
	
    .i_sclgen_scl_pos_edge(scl_pos_edge),
    .i_sclgen_scl_neg_edge(scl_neg_edge),
    
   
	.i_crc_crc_value(i_crc_crc_value),

  
    .o_ddrccc_mode_done(tx_mode_done),
   
	.o_crc_en(o_crc_en),
    .o_crc_parallel_data(o_crc_parallel_data),
	.o_sdahnd_serial_data(o_sdahnd_serial_data)
);

rx dut2 (
	.i_sys_clk(i_sys_clk), //ext
    .i_sys_rst(i_sys_rst), //ext
  
	.i_sclgen_scl(i_sclgen_scl),
    .i_sclgen_scl_pos_edge(scl_pos_edge),
    .i_sclgen_scl_neg_edge(scl_neg_edge),
  
	.i_ddrccc_rx_en(rx_en),  
    .i_ddrccc_rx_mode(rx_mode),
    
	.i_crc_value(i_crc_crc_value),  //ext
    .i_crc_valid(i_crc_valid),  //ext
	
	.i_sdahnd_rx_sda(i_sdahnd_rx_sda), //ext

    
    
    .o_ddrccc_rx_mode_done(rx_mode_done),
    .o_ddrccc_pre(rx_pre),
    .o_ddrccc_error(rx_error),
    
	.o_crc_en(o_crc_en),//ext
    .o_crc_data_valid(o_crc_data_valid),//ext
   
	.o_regfcrc_rx_data_out(o_regfcrc_rx_data_out) //ext
	
);

scl_generation dut3(

	.i_sdr_ctrl_clk(i_sys_clk),
    .i_sdr_ctrl_rst_n(i_sys_rst),
    .i_sdr_scl_gen_pp_od(sdahand_pp_od),
    .i_scl_gen_stall(scl_stall),
    
	.i_sdr_ctrl_scl_idle(i_sdr_ctrl_scl_idle),//ext
    .i_timer_cas(i_timer_cas), //ext

    
    .o_scl_pos_edge(scl_pos_edge),
    .o_scl_neg_edge(scl_neg_edge),
    
	.o_scl(o_scl) //ext
	
);

bits_counter dut4 (
	
	.i_sys_clk(i_sys_clk),
    .i_rst_n(i_sys_rst),
    
	.i_bitcnt_en(bitcnt_en),
    .i_scl_pos_edge(scl_pos_edge),
    .i_scl_neg_edge(scl_neg_edge),
    .i_cccnt_err_rst(bitcnt_rst),

   
    .o_frcnt_toggle(frcnt_toggle),
    .o_cnt_bit_count(cnt_bit_count)  
	
);

frame_counter dut5 (
	.i_fcnt_clk(i_sys_clk),
    .i_fcnt_rst_n(i_sys_rst),	
    .i_regf_CMD_ATTR(i_regf_cmd_attr),
    .i_regf_DATA_LEN(i_regf_DATA_LEN), //ext
    .i_regf_DTT(i_regf_dtt),
	
	.i_fcnt_en(frmcnt_en),
    .i_cnt_bit_count(cnt_bit_count),
    .i_bitcnt_toggle(frcnt_toggle),

	.i_ccc_Direct_Broadcast_n(i_ccc_Direct_Broadcast_n), //ext
   
   
    .o_cccnt_last_frame(frmcnt_last)

);

scl_staller  dut6 (
	
	.i_stall_clk(i_sys_clk),
    .i_stall_rst_n(i_sys_rst),
    
	.i_stall_flag(sclstall_en),
    .i_stall_cycles(sclstall_no_of_cycles),

    
    .o_stall_done(stall_done),
    .o_scl_stall(scl_stall)

);

endmodule 

 `timescale 1us/1ps
 
 module nt_tb ();
 
 // Declare inputs and outputs for DUT
  
  //-----------------ddr-------------// 
    reg           	 i_sys_clk_tb;
    reg           	 i_sys_rst_tb;
    reg            	 i_engine_en_tb;
    reg            	 i_regf_toc_tb;
    reg  [4:0]       i_regf_dev_index_tb;
    reg              i_regf_short_read_tb;
    reg              i_regf_wroc_tb;
    reg              i_regf_wr_rd_bit_tb;
    reg              i_regf_cmd_attr_tb;
    reg   [2:0]      i_regf_dtt_tb;
    wire             o_regf_wr_en_tb;
    wire             o_regf_rd_en_tb;
    wire  [9:0]      o_regf_addr_tb;
    wire             o_engine_done_tb;
    wire             o_regf_abort_tb;
    wire  [3:0]      o_regf_error_type_tb;
	
//------------tx-----------------//	
    reg   [7:0]      i_regf_tx_parallel_data_tb;
  //  reg   [4:0]      i_crc_crc_value_tb;
  //  wire             o_crc_en_tb;
  //  wire  [7:0]      o_crc_parallel_data_tb;
    wire             o_sdahnd_serial_data_tb;
   
 //-------------rx---------------//
    reg              i_sdahnd_rx_sda_tb;
/*	reg              i_crc_valid_tb_tb;
	reg              i_crc_last_byte_tb;
	reg		 [4:0]   i_crc_value_tb;
    wire             o_crc_data_valid_tb;*/
    wire  [7:0]      o_regfcrc_rx_data_out_tb;

//-------------scl---------------//   
    reg              i_sdr_ctrl_scl_idle_tb;
    reg              i_timer_cas_tb;
    wire             o_scl_tb;
   
//-------------frm_cnt---------------//
    reg              i_ccc_Direct_Broadcast_n_tb;
    reg   [15:0]     i_regf_DATA_LEN_tb;

    // Instantiate DUT
    top dut (
        .i_sys_clk(i_sys_clk_tb),
        .i_sys_rst(i_sys_rst_tb),
        .i_engine_en(i_engine_en_tb),
        .i_regf_toc(i_regf_toc_tb),
        .i_regf_dev_index(i_regf_dev_index_tb),
        .i_regf_short_read(i_regf_short_read_tb),
        .i_regf_wroc(i_regf_wroc_tb),
        .i_regf_wr_rd_bit(i_regf_wr_rd_bit_tb),
        .i_regf_cmd_attr(i_regf_cmd_attr_tb),
        .i_regf_dtt(i_regf_dtt_tb),
        .o_regf_wr_en(o_regf_wr_en_tb),
        .o_regf_rd_en(o_regf_rd_en_tb),
        .o_regf_addr(o_regf_addr_tb),
        .o_engine_done(o_engine_done_tb),
        .o_regf_abort(o_regf_abort_tb),
        .o_regf_error_type(o_regf_error_type_tb),
        .i_regf_tx_parallel_data(i_regf_tx_parallel_data_tb),
     //   .i_crc_crc_value(i_crc_crc_value_tb),
     //   .o_crc_en(o_crc_en_tb),
     //   .o_crc_parallel_data(o_crc_parallel_data_tb),
        .o_sdahnd_serial_data(o_sdahnd_serial_data_tb),
		.i_sdahnd_rx_sda(i_sdahnd_rx_sda_tb),
     //   .i_crc_valid(i_crc_valid_tb),
     //   .o_crc_data_valid(o_crc_data_valid_tb),
        .o_regfcrc_rx_data_out(o_regfcrc_rx_data_out_tb),
        .i_sdr_ctrl_scl_idle(i_sdr_ctrl_scl_idle_tb),
        .i_timer_cas(i_timer_cas_tb),
        .o_scl(o_scl_tb),
     //   .i_ccc_Direct_Broadcast_n(i_ccc_Direct_Broadcast_n_tb),
        .i_regf_DATA_LEN(i_regf_DATA_LEN_tb)
    );

   
 // clock generation
parameter CLK_PERIOD = 10; 	 	 
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;



initial 
	begin 
	 
        i_sys_clk_tb = 0;
		i_sys_rst_tb    = 1'b1 ; // not asserted 
	//	i_scl_gen_stall_tb     = 1'b0 ;
		//i_sdr_scl_gen_pp_od_tb = 1;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		i_regf_dev_index_tb = 1;
		i_sdahnd_rx_sda_tb = 0;
		i_regf_toc_tb = 0 ;
		i_regf_short_read_tb = 0;
		
		
		
		
		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b1 ; // not asserted
		
		#(6*CLK_PERIOD);
	
	#(CLK_PERIOD);
	i_engine_en_tb=1;
	i_regf_wr_rd_bit_tb = 0 ;
	i_regf_tx_parallel_data_tb= 'd10;
//	i_crc_crc_value_tb ='b00000;
	//i_regf_dev_index_tb = 1;
	i_regf_cmd_attr_tb = 0;  //regular
	i_regf_DATA_LEN_tb = 5;
	i_regf_dtt_tb = 2;
	i_ccc_Direct_Broadcast_n_tb=0;
 
  
 //#(15*CLK_PERIOD);        
	
//@(o_tx_en_tb == 0);
//#(CLK_PERIOD);
@ (dut.dut0.current_state == 'd9)   ;
i_sdahnd_rx_sda_tb = 1;
@(dut.dut0.current_state == 'd7)  ;

/*@(dut.dut0.current_state == 'd9)  ;
i_sdahnd_rx_sda_tb = 1;

@(dut.dut0.current_state == 'd9)  ;
i_sdahnd_rx_sda_tb = 1;

@(dut.dut0.current_state == 'd12);
i_sdahnd_rx_sda_tb = 1;


/*@(dut.dut0.next_state == 'd15);
i_sdahnd_rx_sda_tb = 1;*/



@(dut.dut0.current_state == 0);
/*i_regf_wr_rd_bit_tb = 1 ;
//i_sdahnd_rx_sda_tb = 1;
@(dut.dut0.o_rx_mode == 3);
repeat (20) begin 
 #(2*CLK_PERIOD);
 i_sdahnd_rx_sda_tb = ~i_sdahnd_rx_sda_tb;
end 
#(50*CLK_PERIOD);
//@(DUT0.next_state == 0);*/
	


#(6*CLK_PERIOD);



		
	
	
	
	
	
	
	
	$stop;
	end



endmodule
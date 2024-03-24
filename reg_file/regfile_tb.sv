module frame_counter_tb ();

/*
1-signal declaration .
2-clk generation .
3-DUT instatiation .
4-initial block .
*/ 


// 1-signal declaration 
	// common signals 
	reg 	 	i_regf_clk_tb = 0 ;
	reg 		i_regf_rst_n_tb ;
	reg 		i_regf_rd_en_tb ;
	reg 		i_regf_wr_en_tb ;
	reg [11:0]  i_regf_addr_tb ;
	reg [7:0]	i_regf_data_wr_tb ;	
	reg [11:0]	i_engine_configuration_tb ;

	wire [15:0]  o_frmcnt_data_len_tb ;
	wire [2:0]   o_cccnt_CMD_ATTR_tb ;
	wire [3:0]	 o_engine_TID_tb ; 	 	
	wire [7:0]   o_ccc_CMD_tb ;
	wire [4:0]	 o_cccnt_DEV_INDEX_tb ;
	wire [2:0]   o_frmcnt_DTT_tb ;
	wire [2:0]	 o_engine_MODE_tb ;
	wire 	 	 o_cccnt_RnW_tb ;
	wire 	 	 o_cccnt_WROC_tb;
	wire 	 	 o_cccnt_TOC_tb;  
	wire 	     o_engine_CP_tb ;

	wire 		 o_ser_rx_tx_tb ;
	wire [7:0]   o_regf_data_rd_tb ;



// 2-clk generation 

	// system clk = 50 Mhz
	parameter CLK_PERIOD = 20 ; 	 	 	 
	always #(CLK_PERIOD/2) i_regf_clk_tb = ~i_regf_clk_tb ;
 
// 3-DUT instatiation 
	

	reg_file DUT (
		.i_regf_clk(i_regf_clk_tb),
		.i_regf_rst_n(i_regf_rst_n_tb),
		.i_regf_rd_en(i_regf_rd_en_tb),
		.i_regf_wr_en(i_regf_wr_en_tb),
		.i_regf_data_wr(i_regf_data_wr_tb),
		.i_regf_addr(i_regf_addr_tb),
		.i_engine_configuration(i_engine_configuration_tb),

		.o_frmcnt_data_len(o_frmcnt_data_len_tb),
		.o_cccnt_CMD_ATTR(o_cccnt_CMD_ATTR_tb),
		.o_engine_TID(o_engine_TID_tb),
		.o_ccc_CMD(o_ccc_CMD_tb),
		.o_cccnt_DEV_INDEX(o_cccnt_DEV_INDEX_tb),
		.o_frmcnt_DTT(o_frmcnt_DTT_tb),
		.o_engine_MODE(o_engine_MODE_tb),
		.o_cccnt_RnW(o_cccnt_RnW_tb),
		.o_cccnt_WROC(o_cccnt_WROC_tb),
		.o_cccnt_TOC(o_cccnt_TOC_tb),
		.o_engine_CP(o_engine_CP_tb),

		.o_ser_rx_tx(),
		.o_regf_data_rd(),
		.o_regf_num_frames(),
		.o_crh_CRHDLY(),
		.o_crh_getstatus_data(),
		.o_crh_CRCAP2(),
		.o_crh_PRECR(),
		.o_crh_cfg_reg(),
		.o_crh_tgts_count(),
		.o_regf_ibi_cfg(),
		.o_regf_ibi_payload_size_reg(),
		.o_i_ibi_tgt_address(),
		.o_regf_hj_cfg(),
		.o_regf_hj_support()

		);
// 4-initial block 
	initial begin 
		// time zero
		i_regf_rst_n_tb    	   = 1'b0 ; //  asserted  			 
		

		#(2* CLK_PERIOD) ;
		i_regf_rst_n_tb    		   = 1'b1 ; // not asserted 
		#(2* CLK_PERIOD) ;
		i_engine_configuration_tb = 'd1000 ;

		i_regf_rd_en_tb 	 	  = 1'b0 ;		
		i_regf_wr_en_tb 		  = 1'b1 ;
		i_regf_addr_tb  		  = 'd1000 ;
		i_regf_data_wr_tb 	 	  = 8'hf1 ;
		#(2* CLK_PERIOD) i_regf_addr_tb  		  = 'd1001 ; i_regf_data_wr_tb 	 	  = 8'h8f ;
		#(2* CLK_PERIOD) i_regf_addr_tb  		  = 'd1002 ; i_regf_data_wr_tb 	 	  = 8'h10 ;
		#(2* CLK_PERIOD) i_regf_addr_tb  		  = 'd1003 ; i_regf_data_wr_tb 	 	  = 8'h18 ;

		#(10*CLK_PERIOD) i_engine_configuration_tb = 'd450 ;



			


		#(500*CLK_PERIOD);







		$stop ;
	end
endmodule 
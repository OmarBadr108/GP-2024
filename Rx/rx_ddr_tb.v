module DDR_TB ();


reg        i_sys_clk_tb;
reg        i_sys_rst_tb;
reg        i_engine_en_tb;
reg        i_sdahnd_rx_sda_tb;
reg        i_frmcnt_last_tb;
reg        i_tx_mode_done_tb;


reg        i_crc_value_tb	;
reg        i_crc_valid_tb	;



reg        i_regf_wr_rd_bit_tb;
//reg        i_rx_error_tb;
reg        i_regf_toc_tb;

reg [4:0]  i_regf_dev_index_tb;
reg        i_regf_short_read_tb;
reg        i_regf_wroc_tb;

 

 wire        o_tx_en_tb;
 wire  [4:0] o_tx_mode_tb;

 wire  [7:0] o_regfcrc_rx_data_out_tb	;
 wire        o_crc_en_tb        		;         
 wire        o_frmcnt_en_tb;
 wire        o_bitcnt_en_tb; // added
 wire        o_bitcnt_rst_tb; // rst the counter due to error 

 wire        o_regf_wr_en_tb;
 wire        o_regf_rd_en_tb;
 wire  [9:0] o_regf_addr_tb;
 wire  [3:0] o_sclstall_no_of_cycles_tb;
 wire        o_sclstall_en_tb;
 wire        o_regf_abort_tb;  
 wire        o_engine_done_tb;
 wire  [3:0] o_regf_error_type_tb ;





wire   ddrccc_rx_en_tb;
wire  [3:0] ddrccc_rx_mode_tb;

wire  ddrccc_rx_mode_tb;

wire  ddrccc_pre_tb;
wire o_ddrccc_error_tb;



RX U0 (
	.i_sys_clk					(i_sys_clk_tb)				,
	.i_sys_rst					(i_sys_rst_tb)				,
	.i_sclgen_scl				(i_sclgen_scl_tb)			,
	.i_sclgen_scl_pos_edge		(i_sclgen_scl_pos_edge_tb)	,
	.i_sclgen_scl_neg_edge		(i_sclgen_scl_neg_edge_tb)	,
	.i_ddrccc_rx_en				(ddrccc_rx_en_tb)			,
	.i_sdahnd_rx_sda			(i_sdahnd_rx_sda_tb)		,
	.i_bitcnt_rx_bit_count		(i_bitcnt_rx_bit_count_tb)	,
	.i_ddrccc_rx_mode			(ddrccc_rx_mode_tb)		,
	.i_crc_value				(i_crc_value_tb)			,
	.i_crc_valid				(i_crc_valid_tb)			,
			
	.o_regfcrc_rx_data_out		(o_regfcrc_rx_data_out_tb)	,
	.o_ddrccc_rx_mode_done		(o_ddrccc_rx_mode_done_tb)	,
	.o_ddrccc_pre				(ddrccc_pre_tb)			,
	.o_ddrccc_error				(o_ddrccc_error_tb)			,
	.o_crc_en					(o_crc_en_tb)                 

);



 ddr_mode DUT0 (
    .i_sys_clk(i_sys_clk_tb),
    .i_sys_rst(i_sys_rst_tb),
    .i_engine_en(i_engine_en_tb),
    .i_frmcnt_last(i_frmcnt_last_tb),
    .i_tx_mode_done(i_tx_mode_done_tb),
   
    .i_rx_mode_done(ddrccc_rx_mode_done_tb),
    .i_rx_pre(o_ddrccc_pre_tb),
    .i_regf_wr_rd_bit(i_regf_wr_rd_bit_tb),
    .i_rx_error(o_ddrccc_error_tb),
    .i_regf_toc(i_regf_toc_tb),
    .i_regf_dev_index(i_regf_dev_index_tb),
	.i_regf_short_read(i_regf_short_read_tb),
	.i_regf_wroc(i_regf_wroc_tb),
    .o_tx_en(o_tx_en_tb),
    .o_tx_mode(o_tx_mode_tb),
    
    .o_rx_en(ddrccc_rx_en_tb),
    .o_rx_mode(ddrccc_rx_mode_tb),
    .o_frmcnt_en(o_frmcnt_en_tb),
    .o_bitcnt_en(o_bitcnt_en_tb),
    .o_bitcnt_rst(o_bitcnt_rst_tb),
    .o_sdahand_pp_od(sdr_scl_gen_pp_od),
    .o_regf_wr_en(o_regf_wr_en_tb),
    .o_regf_rd_en(o_regf_rd_en_tb),
    .o_regf_addr(o_regf_addr_tb),
    .o_sclstall_no_of_cycles(o_sclstall_no_of_cycles_tb),
    .o_sclstall_en(o_sclstall_en_tb),
    .o_regf_abort(o_regf_abort_tb),
    .o_engine_done(o_engine_done_tb),
    .o_regf_error_type(o_regf_error_type_tb)
	
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

 /********clock generation*********/
parameter CLK_PERIOD = 10; 	 	 
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;


initial 
	begin 
	i_sys_clk_tb =0;
	i_sys_rst_tb=0;  
	#1
	i_sys_rst_tb=1; 
    i_scl_gen_stall_tb   =0      ;  
    i_sdr_ctrl_scl_idle_tb =0    ;
    i_timer_cas_tb     =0  ; 
	
	#9
	i_engine_en_tb=1;
	
	
	#24                
	//i_tx_mode_done_tb =0;
	#2            
	
	
	
	
	/************command frame ***********************/
	#18
	i_tx_mode_done_tb =1;
	#2                 //  edge 2  , from 1--->2
	i_tx_mode_done_tb =0;
	
	/***********************************/
	#18
	i_tx_mode_done_tb =1;
	i_regf_wr_rd_bit_tb = 0 ; //write 
	#2                 //  edge 3
	i_tx_mode_done_tb =0;
	
	/***********************************/
	#((7*20)-2)
	i_tx_mode_done_tb =1;
	#2                 //  edge 10 , from 3--->10
	i_tx_mode_done_tb =0;
	/***********************************/
	
	i_regf_dev_index_tb = 1;
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	#2                 //  edge 18   , from 11--->18
	i_tx_mode_done_tb =0;
	/***********************************/
	
	#38 
	i_tx_mode_done_tb =1;
	#2                 //  edge 20  ,from 19--->20
	i_tx_mode_done_tb =0;
	
	
	/***************data frame*******************/
	
	#18 
	i_tx_mode_done_tb =1;
	#2                 //  edge 1
	i_tx_mode_done_tb =0;
	
	/**********************************/
	
	/***check error due to nack**/
	
	/*#18 
	i_rx_mode_done_tb=1;
	i_rx_error_tb = 1;
	#2                 //  edge 2
	i_tx_mode_done_tb =0;*/ 
	
	#18 
	#10                 // added delay one clk cycle due to open drain 
	
	//i_rx_mode_done_tb=1;
	//i_rx_error_tb = 0;         // ideal time for recieving 
	#2                 //  edge 2

		
	//i_rx_mode_done_tb=0;
	//i_rx_error_tb = 0;

	i_regf_wr_rd_bit_tb = 0 ; //write 
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	i_frmcnt_last_tb = 0 ;
	#2                 //  edge 10
	i_tx_mode_done_tb =0;
	
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	i_frmcnt_last_tb = 1;
	#2                 //  edge 18
	i_tx_mode_done_tb =0;
	
	
	#38 
	i_tx_mode_done_tb =1;
	#2                 //  edge 20
	i_tx_mode_done_tb =0;
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	$stop;
	
	
	
	
	end
	endmodule
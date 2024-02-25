module DDR_TB ();

/**********************ddr******************/

reg        i_sys_clk_tb;
reg        i_sys_rst_tb;
reg        i_engine_en_tb;
reg        i_frmcnt_last_tb;
reg        i_tx_mode_done_tb;
reg        i_tx_parity_data_tb;
reg        i_rx_mode_done_tb;
reg        i_rx_pre_tb;
reg        i_regf_wr_rd_bit_tb;
reg        i_rx_error_tb;
reg        i_regf_toc_tb;
reg        i_regf_dev_index_tb;
/*wire [4:0]  i_bitcount_tb;
wire        i_scl_pos_edge_tb;    
wire        i_scl_neg_edge_tb;
wire        scl_tb,*/
 

 wire        o_tx_en_tb;
 wire  [4:0] o_tx_mode_tb;
 wire        o_rx_en_tb;
 wire  [3:0] o_rx_mode_tb;
 wire        o_frmcnt_en_tb;
 wire        o_bitcnt_en_tb; // added
 wire        o_bitcnt_rst_tb; // rst the counter due to error 
 //wire        o_sdahand_pp_od_tb;
 wire        o_regf_wr_en_tb;
 wire        o_regf_rd_en_tb;
 wire  [9:0] o_regf_addr_tb;
 wire  [3:0] o_sclstall_no_of_cycles_tb;
 wire        o_sclstall_en_tb;
 wire        o_regf_abort_tb;  
 wire        o_engine_done_tb;
 wire  [1:0] o_regf_error_type_tb ;

 
 
 /***************bitcnt*******************/
     /* reg       i_sys_clk             ;
      reg       i_rst_n               ;
      reg       i_bitcnt_en           ;  
      reg       i_scl_pos_edge        ;  
      reg       i_scl_neg_edge        ; */ 
     wire  [4:0] o_bitcnt_tb ;
	 
	 
	 
	 /*******************scl***************/
	/* wire i_sdr_ctrl_clk          ;   // 50 MHz clock
    wire       i_sdr_ctrl_rst_n        ;
    wire       i_sdr_scl_gen_pp_od     ;   // 1: Push-Pull      // 0: for Open-Drain*/
    reg       i_scl_gen_stall_tb         ;  // 1 for stalling
    reg       i_sdr_ctrl_scl_idle_tb     ;
    reg       i_timer_cas_tb             ;
    /* reg        o_scl_pos_edge          ;
     reg        o_scl_neg_edge          ;*/
     wire        o_scl_tb ;
	 
     
/*************common***************/

wire pos,neg,sdr_scl_gen_pp_od;




/*********instatiation*******************/
  ddr_mode DUT0 (
    .i_sys_clk(i_sys_clk_tb),
    .i_sys_rst(i_sys_rst_tb),
    .i_engine_en(i_engine_en_tb),
    .i_frmcnt_last(i_frmcnt_last_tb),
    .i_tx_mode_done(i_tx_mode_done_tb),
    .i_tx_parity_data(i_tx_parity_data_tb),
    .i_rx_mode_done(i_rx_mode_done_tb),
    .i_rx_pre(i_rx_pre_tb),
    .i_regf_wr_rd_bit(i_regf_wr_rd_bit_tb),
    .i_rx_error(i_rx_error_tb),
    .i_regf_toc(i_regf_toc_tb),
    .i_regf_dev_index(i_regf_dev_index_tb),
    .o_tx_en(o_tx_en_tb),
    .o_tx_mode(o_tx_mode_tb),
    .o_rx_en(o_rx_en_tb),
    .o_rx_mode(o_rx_mode_tb),
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


bits_counter DUT1(
.i_sys_clk (i_sys_clk_tb)            ,
 .          i_rst_n   (i_sys_rst_tb)            ,
  .        i_bitcnt_en (o_bitcnt_en_tb)          ,  
   .      i_scl_pos_edge (pos)      ,  
    .      i_scl_neg_edge ( neg)      ,  
     .o_cnt_bit_count  (o_bitcnt_tb)
	 );
	 
	 

scl_generation  DUT2 (
.i_sdr_ctrl_clk  (i_sys_clk_tb)        ,   
 .          i_sdr_ctrl_rst_n  (i_sys_rst_tb)      ,
  .        i_sdr_scl_gen_pp_od  (sdr_scl_gen_pp_od)   ,  
   .        i_scl_gen_stall   (i_scl_gen_stall_tb)    ,  // 
    .       i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb)    ,
     .      i_timer_cas   (i_timer_cas_tb)          ,
      .      o_scl_pos_edge  ( pos)      ,
       .     o_scl_neg_edge  (neg)        ,
        .    o_scl (o_scl_tb)
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
	i_tx_mode_done_tb =0;
	#2            //  edge 1
	
	/***********************************/
	#18
	i_tx_mode_done_tb =1;
	#2                 //  edge 2
	i_tx_mode_done_tb =0;
	/***********************************/
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	#2                 //  edge 10
	i_tx_mode_done_tb =0;
	/***********************************/
	
	i_regf_dev_index_tb = 1;
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	i_tx_parity_data_tb =0;
	#2                 //  edge 18
	i_tx_mode_done_tb =0;
	/***********************************/
	
	#38 
	i_tx_mode_done_tb =1;
	#2                 //  edge 20
	i_tx_mode_done_tb =0;
	
	
	/***************new frame*******************/
	
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
	i_rx_mode_done_tb=1;
	i_rx_error_tb = 0;
	#2                 //  edge 2
	i_rx_mode_done_tb=0;
	i_rx_error_tb = 0;

	i_regf_wr_rd_bit_tb = 0 ; //write 
	#((9*20)-2)
	i_tx_mode_done_tb =1;
	#2                 //  edge 10
	i_tx_mode_done_tb =0;
	
	#((8*20)-2)
	i_tx_mode_done_tb =1;
	i_tx_parity_data_tb=1;
	i_frmcnt_last_tb = 0;
	#2                 //  edge 18
	i_tx_mode_done_tb =0;
	
	
	#38 
	i_tx_mode_done_tb =1;
	#2                 //  edge 20
	i_tx_mode_done_tb =0;
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	$stop;
	
	
	
	
	end
	endmodule







 
 
 


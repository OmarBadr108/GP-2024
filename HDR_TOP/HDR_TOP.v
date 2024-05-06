module HDR_TOP (
	// ports are :
	// any thing related to CRC are temporarly considered as ports 
	// system signals like clk and rst and sclgen rst 
	// and of course SDA and SCL

	input 		sys_clk_50mhz                     ,
	input 		i_sdr_rst_n                       ,
	input 	 	hdrengine_en                      ,
	input   	i_sclgen_rst_n_tb                 ,
	input [2:0] i_MODE                            ,
	
	// Configurations signals
    input wire   [7:0]   i_regf_config            ,
    input wire           i_data_config_mux_sel    ,  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
    input wire   [11:0]  i_regf_wr_address_config ,
    input wire           i_regf_wr_en_config      ,

	output   i3cengine_hdrengine_done_tb       ,
	output   hdrengine_exit                    ,
	
	inout    ser_hdr_data                      ,
	output   scl 
	);






////////////////////////////////// HDR BLOCKS //////////////////////////////////
   
   // Internal wires  

 //----------------------- CONFIGURATION SIGNALS------------------------//  
    wire      [11:0]     engine_configuration_addr   ;
    wire      [15:0]     frmcnt_data_len             ; 
    wire      [2:0]      cccnt_CMD_ATTR              ;
    wire      [3:0]      engine_TID                  ; 
    wire      [7:0]      ccc_CMD                     ;
    wire      [4:0]      cccnt_DEV_INDEX             ;
    wire      [2:0]      frmcnt_DTT                  ;
    wire      [2:0]      engine_MODE                 ;
    wire                 cccnt_RnW                   ;
    wire                 cccnt_WROC                  ;
    wire                 cccnt_TOC                   ;
    wire                 engine_CP                   ;

//----------------------------HDR TX SIGNALS----------------------------//
wire [4:0] crc_value;
wire [7:0] crc_parallel_data;
wire       crc_en;
wire       tx_hdr_mode_done;

//----------------------------HDR RX SIGNALS----------------------------//
wire crc_valid;
wire rx_hdr_mode_done;
wire rx_pre;
wire rx_error;
wire crc_data_valid;
wire ddrccc_error_done;

//----------------------------HDR Frame Counter----------------------------//
wire [5:0]  cnt_bit_count;
wire        bitcnt_frcnt_toggle;
wire        frmcnt_last_frame_hdr;

//----------------------------HDR Bit Counter----------------------------//
wire bitcnt_err_rst;


//----------------------------CCC Handler----------------------------//
wire ccc_DBP;
wire cccnt_SRE;  
wire frmcnt_Direct_Broadcast_n;
wire engine_odd;
wire ccc_engine_done ;

wire [7:0]  ccc_tx_special_data ;
wire [3:0]  o_regf_ERR_STATUS_tb ;
   
//----------------------------SCL staller HDR----------------------------//
 wire       scl_stall_done_hdr ;
 wire       o_scl_stall_hdr ;
 wire [4:0] hdr_scl_stall_cycles_mux_out ;
//--------------------------- DDR ----------------------------//
wire        ddr_engine_done ;
wire [7:0]  ddr_tx_special_data ;
wire        bitcnt_rst ;
wire        o_regf_abort ;
wire [3:0]  o_regf_error_type ;
    

 //////////////////////// HDR SIGNALS /////////////////////
 
   wire                  enthdr_en;
   //wire                  hdrengine_en;
   wire                  ser_s_data_mux_out          ;                            // OUT CHOOSE BETWEEN HDR & SDR
   wire                  enthdr_done                 ;
   //wire                  hdrengine_exit              ;
   wire                  enthdr_regf_rd_en           ;
   wire       [11:0]     enthdr_regf_addr            ;
   wire                  enthdr_tx_en                ;
   wire       [2:0]      enthdr_tx_mode              ;  
   wire                  enthdr_rx_en                ;  
   wire       [2:0]      enthdr_rx_mode              ;
   wire                  enthdr_bit_cnt_en           ;
   //wire                  ser_hdr_data                ;
   wire                  regf_wr_en_mode             ; 
   wire                  regf_data_mode              ;
   wire                  regf_rd_en_mode             ; 
   wire                  regf_rd_address_mode        ;
   wire                  scl_pp_od_mode              ;    
   wire                  engine_ccc_enable           ;
   wire                  engine_ddr_enable           ; 

//-------------------------- MUX SEL ------------------------//

 /////////////////////////hdr_mux//////////////////////////

   wire                  ccc_regf_rd_en;                  // out from ccc_block
   wire                  ddr_regf_rd_en;                  // out from ddr_block
   wire                  regf_rd_en_hdr_mux_sel;          //out from hdr_engine 
  
   

   wire                  ccc_regf_wr_en;                 // out from ccc_block
   wire                  ddr_regf_wr_en;                 // out from ddr_block
   wire                  regf_wr_en_hdr_mux_sel;          //out_from hdr_engine 

   wire         [11:0]    ccc_regf_addr;                      // out from ccc_block   
   wire         [11:0]    ddr_regf_addr;                  // out from ddr_block
   wire         [11:0]   regf_rd_address_hdr_mux_out ;
   wire                  regf_rd_address_hdr_mux_sel;          //out_from hdr_engine 

   
   wire                 ccc_tx_en;
   wire                 ddr_tx_en;
   wire                 hdr_tx_en_sel;
   wire                 tx_en_hdr_mux_out;

   wire       [7:0]     cccnt_tx_special_data_mux_out ; // by badr
   wire                 cccnt_tx_special_data_mux_sel ; // by badr

   wire                 ccc_rx_en;
   wire                 ddr_rx_en;
   wire                 hdr_rx_en_sel;
   wire                 rx_en_hdr_mux_out;

   wire        [3:0]    ccc_tx_mode;
   wire        [3:0]    ddr_tx_mode;
   wire                 hdr_tx_mode_sel;
   wire        [3:0]    tx_mode_hdr_mux_out;

   wire        [3:0]    ccc_rx_mode;
   wire        [3:0]    ddr_rx_mode;
   wire                 hdr_rx_mode_sel;
   wire        [3:0]    rx_mode_hdr_mux_out;
   wire        [7:0]    regfcrc_rx_data_out ;

   wire                  scl_ddr_pp_od                 ;
   wire                  scl_ccc_pp_od                 ;
   //assign  scl_ddr_pp_od =1'b0;                         //untill integration
 
   wire                 hdr_sdahand_pp_od_sel;
   wire                 hdr_scl_pp_od_sel;
   wire                 ccc_bit_cnt_en;
   wire                 ddr_bit_cnt_en;
   wire                 hdr_bit_cnt_en_sel;
   wire                 hdr_bit_cnt_en_mux_out;

   wire                 ccc_frm_cnt_en;
   wire                 ddr_frm_cnt_en;  
   
   wire                 hdr_frm_cnt_en_sel;
   wire                 hdr_frm_cnt_en_mux_out;

   wire                 ccc_scl_stall_en;
   wire                 ddr_scl_stall_en;

   wire      [4:0]      ccc_scl_stall_cycles;
   wire      [4:0]      ddr_scl_stall_cycles;

   wire                 hdr_scl_stall_cycles_sel;
   wire                 hdr_scl_stall_en_sel;

   wire                 scl_stall_flag_mux_sel;
   wire                 scl_stall_cycles_mux_sel;
   wire                 hdr_scl_stall_flag_mux_out;





    wire                 scl_pos_edge                ;
    wire                 scl_neg_edge                ;
    wire                 scl_gen_stall               ;
    wire                 stall_flag                  ;
    wire      [3:0]      scl_stall_cycles            ;
    wire                 scl_stall_done              ;
    wire                 sdr_ctrl_scl_idle           ;
    wire                 i3c_scl_idle                ;
    wire      [2:0]      scl_idle_mux_sel            ;
    wire                 sdr_scl_idle_mux_out        ;
    wire                 enthdr_pp_od                ; //for enthdr
 





//-------------- regfile signals ------------------------//
    wire        regf_wr_en_mux_out ;
    wire        regf_rd_en_mux_out ;
    wire [11:0] regf_rd_address_mux_out ;
    wire [7:0]  regf_wr_data_mux_out ;
    wire [7:0]  regf_data_rd ;


    // DUT instantiation
     

hdr_engine u_hdr_engine (
    .i_sys_clk                              (sys_clk_50mhz)           , 
    .i_sys_rst_n                            (i_sdr_rst_n)             ,
        .i_i3cengine_hdrengine_en               (hdrengine_en)            , 
    .i_ccc_done                             (ccc_engine_done)                ,
    .i_ddr_mode_done                        (ddr_engine_done)           ,
    .i_TOC                                  (cccnt_TOC)         , //term of completion if 0 restart/ 1 exit needed for exit
    .i_CP                                   (engine_CP)           , // Cmnd present=1 if CCC 0 for Normal Transcation
    .i_MODE                                 (engine_MODE)           ,
    
    .o_tx_en_sel                            (hdr_tx_en_sel),                   
    .o_rx_en_sel                            (hdr_rx_en_sel),
    .o_tx_mode_sel                          (hdr_tx_mode_sel),
    .o_rx_mode_sel                          (hdr_rx_mode_sel),

    .o_cccnt_tx_special_data_mux_sel        (cccnt_tx_special_data_mux_sel), // by badr

    .o_regf_rd_en_sel                       (regf_rd_en_hdr_mux_sel),
    .o_regf_wr_en_sel                       (regf_wr_en_hdr_mux_sel),
    .o_regf_addr_sel                        (regf_rd_address_hdr_mux_sel),
    .o_scl_pp_od_sel                        (hdr_scl_pp_od_sel),
    .o_bit_cnt_en_sel                       (hdr_bit_cnt_en_sel),
    .o_frm_cnt_en_sel                       (hdr_frm_cnt_en_sel),
    .o_sdahand_pp_od_sel                    (hdr_sdahand_pp_od_sel),
    .o_hdr_scl_stall_en_sel                 (hdr_scl_stall_en_sel),             
    .o_hdr_scl_stall_cycles_sel             (hdr_scl_stall_cycles_sel),
        .o_i3cengine_hdrengine_done             (hdrengine_exit)           ,
    .o_ddrmode_en                           (engine_ddr_enable)           ,
    .o_ccc_en                               (engine_ccc_enable)           ,
    .o_regf_addr_special                    (engine_configuration_addr)    );
 

    CCC_Handler CCC_Handler (
        .i_sys_clk              (sys_clk_50mhz),
        .i_sys_rst              (i_sdr_rst_n),
        .i_engine_en            (engine_ccc_enable),
        .i_bitcnt_number        (cnt_bit_count),
        .i_tx_mode_done         (tx_hdr_mode_done),
        .i_rx_mode_done         (rx_hdr_mode_done),
        .i_rx_pre               (rx_pre),
        .i_sclstall_stall_done  (scl_stall_done_hdr),
        .i_rx_error             (rx_error),
        .i_frmcnt_last_frame    (frmcnt_last_frame_hdr),

        .i_i_regf_RnW             (cccnt_RnW),
        .i_i_regf_CMD_ATTR        (cccnt_CMD_ATTR),
        .i_i_regf_CMD             (ccc_CMD),
        .i_i_regf_DEV_INDEX       (cccnt_DEV_INDEX),
        .i_i_regf_TOC             (cccnt_TOC),
        .i_i_regf_WROC            (cccnt_WROC),
        .i_i_regf_DTT             (frmcnt_DTT),
        .i_i_regf_DBP             (ccc_DBP),      
        .i_i_regf_SRE             (cccnt_SRE),
        

        .o_sclstall_en       (ccc_scl_stall_en),
        .o_sclstall_code        (ccc_scl_stall_cycles),
        
        .o_tx_en                (ccc_tx_en), //editted by laila - done 
        .o_tx_mode              (ccc_tx_mode), //editted by laila - done 
        .o_rx_en                (ccc_rx_en), //editted by laila - done 
        .o_rx_mode              (ccc_rx_mode), //editted by laila -done 

        .o_bitcnt_en            (ccc_bit_cnt_en), // done 
        .o_bitcnt_err_rst       (bitcnt_err_rst), // done 
        .o_frmcnt_en            (ccc_frm_cnt_en), // done 
        .o_sdahand_pp_od        (scl_ccc_pp_od),      // done                    

        .o_frmcnt_Direct_Broadcast_n  (frmcnt_Direct_Broadcast_n),

        .o_regf_wr_en            (ccc_regf_wr_en),                
        .o_regf_rd_en            (ccc_regf_rd_en),             // done   
        .o_regf_addr             (ccc_regf_addr),           // done 
        .o_engine_done(ccc_engine_done),                        // done 
        .o_txrx_addr_ccc         (ccc_tx_special_data),   // done 
        .o_engine_odd(engine_odd),
        .o_regf_ERR_STATUS       (o_regf_ERR_STATUS_tb)    //??? not an input to regfile - yes it's output to the interface (response fifo or testbench)

        );



    DDR_NT DDR_NT (
        .i_sys_clk(sys_clk_50mhz), // done 
        .i_sys_rst(i_sdr_rst_n),  // done 
        .i_engine_en(engine_ddr_enable), // done 
        .i_regf_toc(cccnt_TOC),
        .i_regf_dev_index(cccnt_DEV_INDEX),
        .i_regf_short_read(cccnt_SRE),
        .i_regf_wroc(cccnt_WROC),
        .i_regf_wr_rd_bit(cccnt_RnW),
        .i_regf_cmd_attr(cccnt_CMD_ATTR),   
        .i_regf_dtt(frmcnt_DTT),             // done 

        .i_tx_mode_done(tx_hdr_mode_done),
        .o_tx_en(ddr_tx_en),
        .o_tx_mode(ddr_tx_mode),
        .o_tx_special_data(ddr_tx_special_data),
   
        .i_rx_mode_done(rx_hdr_mode_done),   
        .i_rx_pre(rx_pre),
        .i_rx_error(rx_error),
        .o_rx_en(ddr_rx_en),
        .o_rx_mode(ddr_rx_mode),
   
        .i_frmcnt_last(frmcnt_last_frame_hdr),
        .o_frmcnt_en(ddr_frm_cnt_en),
    
        .i_bitcnt(cnt_bit_count),   // done 
        .o_bitcnt_en(ddr_bit_cnt_en),
        .o_bitcnt_rst(bitcnt_rst),
  
        .o_sdahand_pp_od(scl_ddr_pp_od),
   
        .i_staller_done(scl_stall_done_hdr),
        .o_sclstall_no_of_cycles(ddr_scl_stall_cycles),  
        .o_sclstall_en(ddr_scl_stall_en),
    
        .o_regf_abort(o_regf_abort),
        .o_regf_error_type(o_regf_error_type),  
        .o_regf_wr_en(ddr_regf_wr_en),
        .o_regf_rd_en(ddr_regf_rd_en), // done
        .o_regf_addr(ddr_regf_addr),
        .o_engine_done(ddr_engine_done)
    );




reg_file u_reg_file (
            .i_regf_clk                   (sys_clk_50mhz)            ,
            .i_regf_rst_n                 (i_sdr_rst_n)              ,
            .i_regf_rd_en                 (regf_rd_en_mux_out)       ,
            .i_regf_wr_en                 (regf_wr_en_mux_out)       ,
            .i_regf_addr                  (regf_rd_address_mux_out)  ,
            .i_regf_data_wr               (regf_wr_data_mux_out)     ,

            .i_engine_configuration       (engine_configuration_addr),   
            .o_frmcnt_data_len            (frmcnt_data_len)          ,    // input to : CCC & DDR
            .o_cccnt_CMD_ATTR             (cccnt_CMD_ATTR)           ,
            .o_engine_TID                 (engine_TID)               ,       
            .o_ccc_CMD                    (ccc_CMD)                  ,
            .o_cccnt_DEV_INDEX            (cccnt_DEV_INDEX)          ,
            .o_frmcnt_DTT                 (frmcnt_DTT)               ,
            .o_engine_MODE                (engine_MODE)              ,
            .o_cccnt_RnW                  (cccnt_RnW)                ,
            .o_cccnt_WROC                 (cccnt_WROC)               ,
            .o_cccnt_TOC                  (cccnt_TOC)                ,
            .o_engine_CP                  (engine_CP)                ,
            
            // badr 
            // these two are missing      which means this regfile is different from mine      
            .o_cccnt_DBP                  (ccc_DBP),   //done -Laila
            .o_cccnt_SRE                  (cccnt_SRE),   //done -Laila
            
            .o_regf_data_rd               (regf_data_rd)             ,
            .o_ser_rx_tx                  ()                ,
            .o_regf_num_frames            ()             ,
            .o_crh_CRHDLY                 ()               ,
            .o_crh_getstatus_data         ()       ,
            .o_crh_CRCAP2                 ()               ,
            .o_crh_PRECR                  ()                ,
            .o_crh_cfg_reg                ()              ,
            .o_crh_tgts_count             ()           ,
            .o_regf_ibi_cfg               ()            ,
            .o_regf_ibi_payload_size_reg  ()    ,
            .o_i_ibi_tgt_address          ()         ,
            .o_regf_hj_cfg                ()               ,
            .o_regf_hj_support            ()          );

/*
// sdr staller
scl_staller u_scl_staller(
.i_stall_clk(sys_clk_50mhz),
.i_stall_rst_n(i_sdr_rst_n),
.i_stall_flag(scl_stall_flag_mux_out),
.i_stall_cycles(scl_stall_cycles_mux_out),
.o_stall_done(scl_stall_done),
.o_scl_stall (scl_gen_stall) );
*/

// hdr staller 
    scl_staller scl_staller_hdr (
         .i_stall_clk(sys_clk_50mhz), 
         .i_stall_rst_n(i_sdr_rst_n),
         .i_stall_flag(hdr_scl_stall_flag_mux_out),
         .i_stall_cycles(hdr_scl_stall_cycles_mux_out),
         .o_stall_done(scl_stall_done_hdr),
         .o_scl_stall(o_scl_stall_hdr)
    ); 


    bits_counter bits_counter_hdr (
        .i_sys_clk       (sys_clk_50mhz),
        .i_rst_n         (i_sdr_rst_n),
        .i_bitcnt_en     (hdr_bit_cnt_en_mux_out),
        .i_scl_pos_edge  (scl_pos_edge),
        .i_scl_neg_edge  (scl_neg_edge),
        .i_cccnt_err_rst (bitcnt_err_rst),
        .o_frcnt_toggle  (bitcnt_frcnt_toggle),
        .o_cnt_bit_count (cnt_bit_count)
        
    );
 
        frame_counter frame_counter_hdr (
        //.i_fcnt_no_frms (i_fcnt_no_frms_tb),
        .i_fcnt_clk               (sys_clk_50mhz),
        .i_fcnt_rst_n             (i_sdr_rst_n),
        .i_fcnt_en                (hdr_frm_cnt_en_mux_out),
        .i_regf_CMD_ATTR          (cccnt_CMD_ATTR[0]),
        .i_regf_DATA_LEN          (frmcnt_data_len),
        .i_regf_DTT               (frmcnt_DTT),
        .i_cnt_bit_count          (cnt_bit_count),
        .i_bitcnt_toggle          (bitcnt_frcnt_toggle),
        .o_cccnt_last_frame       (frmcnt_last_frame_hdr)                     

    );




        RX RX (
        .i_sys_clk                  (sys_clk_50mhz)               ,
        .i_sys_rst                  (i_sdr_rst_n)             ,
        .i_sclgen_scl               (scl)                   ,
        .i_sclgen_scl_pos_edge      (scl_pos_edge)           ,
        .i_sclgen_scl_neg_edge      (scl_neg_edge)           ,
        .i_ddrccc_rx_en             (rx_en_hdr_mux_out)                ,
        .i_sdahnd_rx_sda            (deser_s_data)        , // to be put on mux in   //check this signal -Laila
        //.i_bitcnt_rx_bit_count    (i_bitcnt_rx_bit_count_tb)  ,
        .i_ddrccc_rx_mode           (rx_mode_hdr_mux_out)              ,
        .i_crc_value                (crc_value)            ,
        .i_crc_valid                (crc_valid)            ,
            
        .o_regfcrc_rx_data_out      (regfcrc_rx_data_out)         ,
        .o_ddrccc_rx_mode_done      (rx_hdr_mode_done)         ,
        .o_ddrccc_pre               (rx_pre)               ,
        .o_ddrccc_error             (rx_error)             ,
        .o_crc_en                   (crc_en)               , // 
        .o_crc_data_valid           (crc_data_valid)       ,
        .o_ddrccc_error_done        (ddrccc_error_done)      

        );

        tx tx (
        .i_sys_clk               (sys_clk_50mhz),
        .i_sys_rst               (i_sdr_rst_n),
        .i_ddrccc_tx_en          (tx_en_hdr_mux_out),
        .i_sclgen_scl_pos_edge   (scl_pos_edge),
        .i_sclgen_scl_neg_edge   (scl_neg_edge),
        .i_ddrccc_tx_mode        (tx_mode_hdr_mux_out),
        .i_regf_tx_parallel_data (regf_data_rd),
        .i_ddrccc_special_data   (cccnt_tx_special_data_mux_out),  
        .i_crc_crc_value         (crc_value),
        .o_sdahnd_serial_data    (ser_hdr_data),
        .o_ddrccc_mode_done      (tx_hdr_mode_done),
        .o_crc_parallel_data     (crc_parallel_data),
        .o_crc_en                (crc_en)
        );




scl_generation u_scl_generation (
            .i_sdr_ctrl_clk               (sys_clk_50mhz)            ,
            .i_sdr_ctrl_rst_n             (i_sdr_rst_n)              ,
            .i_sdr_scl_gen_pp_od          (scl_pp_od_mux_out)        ,
            .i_scl_gen_stall              (o_scl_stall_hdr)          , 
            .i_sdr_ctrl_scl_idle          (sdr_scl_idle_mux_out )    ,
            .i_timer_cas                  (timer_cas)                ,
            .o_scl_pos_edge               (scl_pos_edge)             ,
            .o_scl_neg_edge               (scl_neg_edge)             ,
            .o_scl                        (scl)                     );
       
scl_generation u_scl_generation_for_tx_only (
            .i_sdr_ctrl_clk               (sys_clk_50mhz)            ,
            .i_sdr_ctrl_rst_n             (i_sdr_rst_n)              ,
            .i_sdr_scl_gen_pp_od          (scl_pp_od_mux_out)        ,
            .i_scl_gen_stall              (1'b0)            , 
            .i_sdr_ctrl_scl_idle          (sdr_scl_idle_mux_out )    ,
            .i_timer_cas                  (timer_cas)                ,
            .o_scl_pos_edge               (scl_pos_edge)             ,
            .o_scl_neg_edge               (scl_neg_edge)             ,
            .o_scl                        (scl)                     );


//////////////////hdr_muxes/////////////////////




gen_mux #(8,1) regf_special_data_hdr_mux (
            .data_in  ({ ccc_tx_special_data, ddr_tx_special_data}),            
            .ctrl_sel (cccnt_tx_special_data_mux_sel)  ,
            .data_out (cccnt_tx_special_data_mux_out) );

gen_mux #(1,1) regf_rd_en_hdr_mux (
            .data_in  ({ ccc_regf_rd_en, ddr_regf_rd_en}),            
            .ctrl_sel (regf_rd_en_hdr_mux_sel)  ,
            .data_out (regf_rd_en_hdr_mux_out) );


gen_mux #(1,1) regf_wr_en_hdr_mux (
            .data_in  ({ ccc_regf_wr_en, ddr_regf_wr_en}),             
            .ctrl_sel (regf_wr_en_hdr_mux_sel)  ,
            .data_out (regf_wr_en_hdr_mux_out) );

gen_mux #(12,1) regf_rd_address__hdr_mux (
            .data_in  ({ ccc_regf_addr, ddr_regf_addr}),
            .ctrl_sel (regf_rd_address_hdr_mux_sel)  ,
            .data_out (regf_rd_address_hdr_mux_out) );

gen_mux #(1,1) tx_en_hdr_mux (
            .data_in  ({ccc_tx_en, ddr_tx_en}),             
            .ctrl_sel (hdr_tx_en_sel)  ,
            .data_out (tx_en_hdr_mux_out) );

gen_mux #(1,1) rx_en_hdr_mux (
            .data_in  ({ccc_rx_en, ddr_rx_en}),             
            .ctrl_sel (hdr_rx_en_sel)  ,
            .data_out (rx_en_hdr_mux_out) );

gen_mux #(4,1) tx_mode_hdr_mux (
            .data_in  ({ccc_tx_mode, ddr_tx_mode}),             
            .ctrl_sel (hdr_tx_mode_sel)  ,
            .data_out (tx_mode_hdr_mux_out) );

gen_mux #(4,1) rx_mode_hdr_mux (
            .data_in  ({ccc_rx_mode, ddr_rx_mode}),             
            .ctrl_sel (hdr_rx_mode_sel)  ,
            .data_out (rx_mode_hdr_mux_out) );


gen_mux #(1,1) scl_pp_od_hdr_mux (
            .data_in  ({scl_ccc_pp_od, scl_ddr_pp_od}),             
            .ctrl_sel (hdr_scl_pp_od_sel)  ,
            .data_out (scl_pp_od_hdr_mux_out) );                

gen_mux #(1,1) bit_cnt_hdr_mux (
            .data_in  ({ccc_bit_cnt_en, ddr_bit_cnt_en}),             
            .ctrl_sel (hdr_bit_cnt_en_sel)  ,
            .data_out (hdr_bit_cnt_en_mux_out) );

gen_mux #(1,1) frm_cnt_hdr_mux (
            .data_in  ({ccc_frm_cnt_en, ddr_frm_cnt_en}),             
            .ctrl_sel (hdr_frm_cnt_en_sel)  ,
            .data_out (hdr_frm_cnt_en_mux_out) );

gen_mux #(1,1) scl_stall_flag_hdr_mux (                             //stall flag
            .data_in  ({ccc_scl_stall_en, ddr_scl_stall_en}),             
            .ctrl_sel (hdr_scl_stall_en_sel)  ,
            .data_out (hdr_scl_stall_flag_mux_out) );



gen_mux #(5,1) scl_stall_cycles_hdr_mux (
            .data_in  ({ccc_scl_stall_cycles, ddr_scl_stall_cycles}),            
            .ctrl_sel (hdr_scl_stall_cycles_sel)  ,
            .data_out (hdr_scl_stall_cycles_mux_out) );



//------------------- higher level of muxes ---------------// 
//////////////reg_file(Config /data write)///////////////////

gen_mux #(1,1) reg_wr_en_config_data_mux (
            .data_in  ({i_regf_wr_en_config,regf_wr_en_hdr_mux_out}),        
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_wr_en_mux_out));

gen_mux #(1,1) reg_rd_en_config_data_mux (
            .data_in  ({i_regf_rd_en_config,regf_rd_en_hdr_mux_out}),        
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_rd_en_mux_out));

gen_mux #(12,1) regf_rd_address_config_data_mux (
            .data_in  ({i_regf_wr_address_config,regf_rd_address_hdr_mux_out}),
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_rd_address_mux_out) );

gen_mux #(8,1) regf_wr_data_config_data_mux (
            .data_in  ({i_regf_config ,regfcrc_rx_data_out }),
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_wr_data_mux_out) );




endmodule 
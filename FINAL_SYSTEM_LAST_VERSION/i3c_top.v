

/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Omar Maghraby, Laila Tamer 
 
 Revision:   

 Version : 1.0

 Create Date: 
 Design Name:  
 Module Name:  

==================================================================================

  STATEMENT OF USE

  This information contains confidential and proprietary information of MIXEL.
  No part of this information may be reproduced, transmitted, transcribed,
  stored in a retrieval system, or translated into any human or computer
  language, in any form or by any means, electronic, mechanical, magnetic,
  optical, chemical, manual, or otherwise, without the prior written permission
  of MIXEL.  This information was prepared for Garduation Project purpose and is for
  use by MIXEL Engineers only.  MIXEL and ASU 2023 GP reserves the right 
  to make changes in the information at any time and without notice.

==================================================================================
//////////////////////////////////////////////////////////////////////////////////*/


`default_nettype none

module I3C_TOP (
    input  wire          i_sdr_clk           , // system clk
    input  wire          i_sdr_rst_n         , // asynch neg edge reset
    input  wire          i_controller_en     , // from device configuration of Controller/Target role
    input  wire          i_i3c_i2c_sel       , // sdr/i2c blocks selector
    input  wire          i_ccc_en_dis_hj     , // (TBD) for enable/disable events to prevent Bus-Initialization or DAA interruptions.
    
    //input wire           i_sclgen_rst_n , // new by badr 

    // Configurations signals
    input wire   [7:0]   i_regf_config  ,
    input wire           i_data_config_mux_sel,  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  

    input wire   [11:0]  i_regf_wr_address_config,
    input wire           i_regf_wr_en_config     ,
    input wire           i_regf_rd_en_config     ,

    inout  wire          sda                 , // sda line
    
    output wire          scl                 , // scl bus
    output wire          o_sdr_rx_valid      , // output to host >> valid data are loaded
    output wire          o_ctrl_done         ); // sdr block done signal


//-- top module wires

//////////////////  controller_tx wires   //////////////////////////
    wire                 sdr_tx_en                   ;
    wire      [2:0]      sdr_tx_mode                 ;
    wire                 i2c_tx_en                   ;
    wire      [2:0]      i2c_tx_mode                 ;
    wire                 i3c_tx_en                   ;
    wire      [2:0]      i3c_tx_mode                 ;
    wire                 daa_tx_en                   ;
    wire      [2:0]      daa_tx_mode                 ;
    wire                 hj_tx_en                    ;
    wire      [2:0]      hj_tx_mode                  ;
    wire                 sdr_ctrl_ser_valid          ;
    wire                 stop_pattern                ;
    wire                 start_pattern               ;
    wire                 ser_s_data                  ;
    wire                 ser_mode_done               ;
    wire                 ser_pp_mode_done            ;
    wire                 ser_to_parity_transition    ;

//////////////////  controller_rx wires   //////////////////////////
    wire                 sdr_rx_en                   ;
    wire      [2:0]      sdr_rx_mode                 ;
    wire                 i2c_rx_en                   ;
    wire      [2:0]      i2c_rx_mode                 ;
    wire                 daa_rx_en                   ;
    wire      [2:0]      daa_rx_mode                 ;
    wire                 hj_rx_en                    ;
    wire      [2:0]      hj_rx_mode                  ;
    wire                 deser_s_data                ;
    wire                 ser_nack_ack                ;
    wire                 sdr_rx_rd_abort             ;
    wire                 rx_mode_done                ;
    wire                 rx_arbitration_lost         ;


///////////////////// bits_counter wires ///////////////////////////
    wire                 i3c_bit_cnt_en              ;
    wire                 sdr_bit_cnt_en              ;
    wire                 sdr_bit_rx_cnt_en           ;
    wire                 i2c_bit_cnt_en              ;
    wire                 i2c_bit_rx_cnt_en           ;
    wire                 daa_bits_cnt_en             ;
    wire                 daa_rx_cnt_en               ;
    wire                 hj_bit_cnt_en               ;
    wire                 sdr_ctrl_cnt_done           ;
    wire      [2:0]      sdr_cnt_bit_count           ;
    wire                 sdr_ctrl_addr_done          ;

/////////////////////  frame_counter wires   ///////////////////////
    wire      [7:0]      fcnt_no_frms                ;
    wire      [7:0]      daa_fcnt_no_frms            ;
    wire      [7:0]      fcnt_no_frms_mux_out        ;
    wire                 sdr_fcnt_en                 ;
    wire                 i2c_fcnt_en                 ;
    wire                 daa_fcnt_en                 ;
    wire                 sdr_ctrl_last_frame         ;

/////////////////  sda_handling/scl_gen wires   ////////////////////
    wire                 i3c_pp_od                   ;
    wire                 sdr_pp_od                   ;
    wire                 i2c_pp_od                   ;
    wire                 daa_pp_od                   ;
    wire                 hj_pp_od                    ;
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

/////////////////////  reg_file wires   ////////////////////////////
    wire                 i3c_regf_rd_en              ;
    wire                 sdr_regf_rd_en              ;
    wire                 i2c_regf_rd_en              ;
    wire                 daa_regf_rd_en              ;
    wire                 hj_regf_rd_en               ;
    wire      [11:0]      sdr_regf_addr               ;
    wire      [11:0]      i2c_regf_addr               ;
    wire      [11:0]      daa_regf_addr               ;
    wire      [11:0]      hj_regf_addr                ;
    wire      [7:0]      regf_data_rd                ;
    wire                 ser_rx_tx                   ;
    wire                 i3c_rx_valid                ;
    wire                 sdr_rx_valid                ;
    wire                 i2c_rx_valid                ;
    wire                 regf_wr_en                  ;
    wire      [7:0]      regf_data_wr                ;
    wire                 daa_regf_wr_en              ;
    wire      [7:0]      daa_regf_data_wr            ;

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
 
////////////////////// IBI wires ////////////////////////////////
    wire         [7:0]   regf_ibi_cfg               ;
    wire         [7:0]   ibi_payload_size_reg       ;
    wire         [7:0]   ibi_tgt_address            ;
    wire                 ibi_done                   ;
    wire                 ibi_en                     ;
    wire                 ibi_payload_en             ;
    wire                 sdr_ctrl_ibi_payload_en    ;
    wire                 sdr_ctrl_ibi_done          ;
    wire                 sdr_ibi_payload_done       ;

    wire                 ibi_regf_rd_en         ;
    wire                 ibi_regf_wr_en         ;
    wire         [11:0]   ibi_regf_address    ;
    wire                 ibi_pp_od              ;
    wire                 ibi_rx_en              ;
    wire                 ibi_tx_en              ;
    wire         [2:0]   ibi_tx_mode            ;
    wire         [2:0]   ibi_rx_mode            ;
    wire                 i3c_ibi_en_tb          ;
    wire                 ibi_cnt_en             ;
    wire                 ibi_ser_rx_tx          ;


/////////////////////  i2c/i3c wires   /////////////////////////////
    wire                 sdr_en                      ;
    wire                 i2c_en                      ;
    wire                 sdr_done                    ;
    wire                 i2c_done                    ;
    wire                 target_nack                 ;

////////////////////// I3C Timer wires /////////////////////////////
   wire                  chr_set                     ;
   wire       [1:0]      crh_entasx                  ;
   wire                  i3c_idle_flag               ;
   wire                  timer_cas                   ;
   wire                  timer_bus_free_pure         ;
   wire                  timer_bus_free_mix_fm       ;
   wire                  timer_bus_free_mix_fm_p     ;
   wire                  timer_bus_aval              ;
   wire                  timer_bus_idle              ;
   wire                  timer_crhpol                ;
   wire                  timer_newcrlck_i2c          ;
   wire                  timer_newcrlck_i3c          ;

/////////////////////// DAA wires /////////////////////////////////
   wire                  daa_en                      ;
   wire                  tx_daa_done                 ;
   wire                  daa_done                    ;
   wire                  daa_error                   ;
   wire       [7:0]      daa_regf_wr_data            ;
   wire                  hj_daa_en                   ;
   wire                  daa_stall_flag    ;
   wire [3:0]            daa_stall_cycles  ;


////////////////////// Hot-Join wires //////////////////////////////
   wire                  hj_en                       ;
   wire                  hj_done                     ;
   wire                  hj_acc_rej                  ;
   wire                  hj_daa_req                  ;
   wire                  hj_cr_pass                  ;
   wire                  hj_ccc                      ;
   wire       [2:0]      hj_cfg_reg                  ;
   wire                  hj_support_reg              ;


///////////////////////// CRH wires ////////////////////////////////
   wire                  hj_crh_en                   ;
   wire                  crh_en                      ;
   wire                     crh_done                    ;
   wire                          crh_ncr_win                 ;
   wire                        crh_ncr_take_control        ;
   wire                        crh_pp_od                   ;
   wire                          crh_cnt_en                  ;
   wire                         crh_rx_cnt_en               ;
   wire                        crh_fcnt_en                 ;
   wire       [7:0]         crh_CRHDLY                   ;
   wire       [7:0]         crh_getstatus_data           ;
   wire       [7:0]         crh_CRCAP2                   ;
   wire       [7:0]         crh_PRECR                    ;
   wire       [7:0]         crh_tgts_count               ;
   wire       [7:0]      crh_cfg_reg;
   wire                              crh_sda_low                 ;
   wire                  crh_rx_pp_mode_done         ;
   wire                  crh_start_detected          ;
   wire                  crh_tx_en                   ;
   wire       [2:0]      crh_tx_mode                 ;
   wire                  crh_rx_en                   ;
   wire       [2:0]      crh_rx_mode                 ;
   wire                  crh_regf_wr_en              ;
   wire                  crh_regf_rd_en              ;
   wire       [11:0]      crh_regf_addr               ;
   wire                  crh_timer_set               ;
   wire                  crh_scl_idle      ;
   wire                  crh_send_stop     ;
   wire                  crh_stop_is_sent  ;



//////////////////////Mux Selection wires //////////////////////////
   wire       [2:0]      regf_rd_en_mux_sel          ;
   wire       [2:0]      regf_wr_en_mux_sel          ;
   wire                  regf_wr_data_mux_sel        ;
   wire       [2:0]      regf_rd_address_mux_sel     ;
   wire       [2:0]      scl_pp_od_mux_sel           ;
   wire       [2:0]      sdr_tx_en_mux_sel               ;
   wire       [2:0]      tx_mode_mux_sel             ;
   wire       [2:0]      rx_en_mux_sel               ;
   wire       [2:0]      rx_mode_mux_sel             ;
   wire       [2:0]      bit_cnt_en_mux_sel          ;
   wire       [2:0]      bit_rx_cnt_en_mux_sel       ;
   wire       [2:0]      fcnt_en_mux_sel             ;
   wire       [2:0]      fcnt_no_frms_sel            ;
   wire       [2:0]      sdr_scl_stall_flag_sel          ;
   wire       [2:0]      sdr_scl_stall_cycles_sel        ;
   wire       [2:0]      ser_rx_tx_mux_sel           ;
   wire       [2:0]      bits_cnt_regf_rx_tx_sel     ;







////////////////////// Mux output wires ////////////////////////////
   wire                  regf_rd_en_mux_out          ;
   wire                  regf_wr_en_mux_out          ;

   wire                  regf_wr_en_mode_mux_out      ;
   wire                  regf_rd_en_mode_mux_out      ;

   wire       [7:0]      regf_wr_data_mode_mux_out    ;
   wire       [7:0]      regf_wr_data_mux_out         ;

   wire       [11:0]     regf_rd_address_mode_mux_out ;
   wire       [11:0]     regf_rd_address_mux_out     ;

   wire                  scl_pp_od_mux_out           ;
   wire                  rx_en_mux_out               ;
   wire                  sdr_tx_en_mux_out               ;
   wire       [2:0]      tx_mode_mux_out             ;
   wire       [2:0]      rx_mode_mux_out             ;
   wire                  bit_cnt_en_mux_out          ;
   wire                  bit_rx_cnt_en_mux_out       ;
   wire                  fcnt_en_mux_out             ;
   wire                  bits_cnt_regf_rx_tx_mux_out ;
   wire                  scl_stall_flag_mux_out      ;
   wire      [4:0]       scl_stall_cycles_mux_out    ; //output of final mux and input to staller -laila
   wire      [4:0]       sdr_scl_stall_cycles_mux_out; //output of sdr mux -laila
   wire                  ser_rx_tx_bits_count_mux_out ; /// for handling from IBI to SDR transition
   wire                  sdr_scl_stall_flag_mux_out;

            
//////////////////////// clk divider ///////////////////////////////
   wire                  sys_clk_50mhz    ;
//////////////////////// HDR SIGNALS /////////////////////
   wire                  enthdr_en;
   wire                  hdrengine_en;
   wire                  ser_s_data_mux_out          ;                            // OUT CHOOSE BETWEEN HDR & SDR
   wire                  enthdr_done                 ;
   wire                  hdrengine_exit              ;
   wire                  enthdr_regf_rd_en           ;
   wire       [11:0]     enthdr_regf_addr            ;
   wire                  enthdr_tx_en                ;
   wire       [2:0]      enthdr_tx_mode              ;  
   wire                  enthdr_rx_en                ;  
   wire       [2:0]      enthdr_rx_mode              ;
   wire                  enthdr_bit_cnt_en           ;
   wire                  ser_hdr_data                ;
   wire                  regf_wr_en_mode             ; 
   wire                  regf_data_mode              ;
   wire                  regf_rd_en_mode             ; 
   wire                  regf_rd_address_mode        ;
   wire                  scl_pp_od_mode              ;    
   wire                  engine_ccc_enable           ;
   wire                  engine_ddr_enable           ; 

///////////////////////////hdr_sdr_mux///////////////////////
   wire                  sda_sel                     ;                // CHOOSE BETWEEN HDR & SDR 
   wire                  regf_rd_en_hdr_mux_out      ; 
   wire                  regf_rd_en_sdr_mux_out      ; 

   wire                  scl_pp_od_hdr_mux_out       ;
   wire                  scl_pp_od_sdr_mux_out       ;
   //wire                  scl_gen_stall_mux_out       ; // new by badr

   wire                  regf_wr_en_hdr_mux_out      ; 
   wire                  regf_wr_en_sdr_mux_out      ;

   wire     [7:0]        regf_wr_data_sdr_mux_out    ;
   wire     [7:0]        regfcrc_rx_data_out         ;               // HDR_RX_DATA_OUT


   wire     [11:0]       regf_rd_address_sdr_mux_out ;
   wire     [11:0]       regf_rd_address_hdr_mux_out ;


 /////////////////////////hdr_mux//////////////////////////

   wire                  ccc_regf_rd_en;                  // out from ccc_block
   wire                  ddr_regf_rd_en;                  // out from ddr_block
   wire                  regf_rd_en_hdr_mux_sel;          //out from hdr_engine 
  
   

   wire                  ccc_regf_wr_en;                 // out from ccc_block
   wire                  ddr_regf_wr_en;                 // out from ddr_block
   wire                  regf_wr_en_hdr_mux_sel;          //out_from hdr_engine 

   wire         [11:0]    ccc_regf_addr;                      // out from ccc_block   
   wire         [11:0]    ddr_regf_addr;                  // out from ddr_block
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

   wire        [2:0]    ccc_rx_mode;
   wire        [2:0]    ddr_rx_mode;
   wire                 hdr_rx_mode_sel;
   wire        [2:0]    rx_mode_hdr_mux_out;

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
   wire      [4:0]      hdr_scl_stall_cycles_mux_out;


   wire                 crc_rx_tx_mux_sel_ccc_nt_sel;

   wire tx_en_sel;
   wire tx_en_mux_out;

   ////////////////////////////////// HDR BLOCKS //////////////////////////////////
   wire o_int_regf_Dummy_conf ; ///// new    17 / 6 / 2024
   // Internal wires  

//----------------------------HDR TX SIGNALS----------------------------//
wire [4:0] crc_value;
wire [7:0] tx_crc_parallel_data;
wire       tx_crc_en;

wire       tx_hdr_mode_done;

//----------------------------HDR RX SIGNALS----------------------------//
wire crc_valid;
wire rx_hdr_mode_done;
wire rx_pre;
wire rx_error;
wire crc_data_valid;
wire ddrccc_error_done;
wire       rx_crc_en;
wire crc_last_byte;

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


wire [3:0] o_regf_ERR_STATUS_tb ;
wire [7:0] ccc_tx_special_data;
wire [7:0] ddr_tx_special_data;
   
//----------------------------SCL staller HDR----------------------------//
 wire scl_stall_done_hdr ;
 wire o_scl_stall_hdr ;

//--------------------------- DDR ----------------------------//
wire        ddr_engine_done ;
wire        bitcnt_rst ;
wire        o_regf_abort ;
wire [3:0]  o_regf_error_type ;

//-----------------------------CRC----------------------------//
//wire crc_en_rx_tx_mux_sel;
wire crc_en_mux_out;

wire tx_crc_data_valid;
wire rx_crc_data_valid;
wire crc_data_valid_mux_out;
//wire crc_data_rx_tx_valid_sel;
//wire       crc_data_tx_rx_mux_sel;
//wire      crc_last_byte_tx_rx_mux_sel;
wire [7:0] crc_data_mux_out;
wire       crc_last_byte_mux_out;


wire       crc_rx_tx_mux_sel_NT;
wire       crc_rx_tx_mux_sel_ccc;

wire       crc_rx_tx_mux_sel_ccc_nt_out;
//-------------------------- SCL not stalled ------------------//

wire scl_not_stalled;
wire scl_neg_edge_not_stalled;
wire scl_pos_edge_not_stalled;


assign o_sdr_rx_valid = regf_wr_en_mux_out ;

i3c_engine u_i3c_engine (
            .i_clk                        (sys_clk_50mhz)            ,
            .i_rst_n                      (i_sdr_rst_n)              ,
            .i_controller_en              (i_controller_en)          ,
            .i_i3c_i2c_sel                (i_i3c_i2c_sel)            ,
            .i_sdr_done                   (sdr_done)                 ,
            .i_i2c_done                   (i2c_done)                 ,
            .i_daa_done                   (daa_done)                 ,
            .i_daa_error                  (daa_error)                ,
            .i_hj_done                    (hj_done)                  ,
            .i_hj_acc_rej                 (hj_acc_rej)               ,
            .i_hj_daa_req                 (hj_daa_req)               ,
            .i_hj_cr_pass                 (hj_cr_pass)               ,
            .i_tx_mode_done               (ser_mode_done)            ,
            .i_rx_mode_done               (rx_mode_done)             ,
            .i_target_nack                (target_nack)              ,
            .i_rx_arbitration_lost        (rx_arbitration_lost)      ,
            .i_scl_pos_edge               (scl_pos_edge)             ,
            .i_scl_neg_edge               (scl_neg_edge)             ,
            .i_regf_data_rd               (regf_data_rd)             ,
            .i_timer_cas                  (timer_cas)                ,
            .i_ccc_en_dis_hj              (i_ccc_en_dis_hj)          ,
            .i_ibi_payload_en             (ibi_payload_en)           ,
            .i_sdr_ibi_payload_done       (sdr_ibi_payload_done)     ,

            .i_crh_done                   (crh_done)                 ,
            //.i_crh_ncr_win                (crh_ncr_win)              ,
            //.i_crh_ncr_take_control       (crh_ncr_take_control)     ,
            .i_crh_send_stop              (crh_send_stop)            ,
            .i_ibi_done                   (ibi_done)                 ,
            ////////////////////////HDR///////////////////////////////
            .i_regf_mode   (engine_MODE)                             ,
            .i_enthdr_done(enthdr_done)                              ,
                                                                                                .i_hdrengine_done (hdrengine_exit)                       ,

            .o_sdr_en                     (sdr_en)                   ,
            .o_i2c_en                     (i2c_en)                   ,
            .o_daa_en                     (daa_en)                   ,
            .o_ibi_en                     (ibi_en)                   ,
            .o_crh_en                     (crh_en)                   ,
            .o_crh_stop_is_sent           (crh_stop_is_sent)         ,
            .o_hj_en                      (hj_en)                    ,
            .o_hj_ccc                     (hj_ccc)                   ,
            .o_hj_daa_en                  (hj_daa_en)                ,
            .o_hj_crh_en                  (hj_crh_en)                ,
            .o_tx_en                      (i3c_tx_en)                ,
            .o_tx_mode                    (i3c_tx_mode)              ,
            .o_pp_od                      (i3c_pp_od)                ,
            .o_scl_idle                   (i3c_scl_idle)             ,
            .o_rx_data_valid              (i3c_rx_valid)             ,
            .o_bit_cnt_en                 (i3c_bit_cnt_en)           ,
            .o_regf_rd_en                 (i3c_regf_rd_en)           ,
            .o_i3c_idle_flag              (i3c_idle_flag)            ,
            .o_regf_rd_en_mux_sel         (regf_rd_en_mux_sel)       ,
            .o_regf_rd_address_mux_sel    (regf_rd_address_mux_sel)  ,
            .o_regf_wr_en_mux_sel         (regf_wr_en_mux_sel)       ,
            .o_scl_pp_od_mux_sel          (scl_pp_od_mux_sel)        ,
            .o_tx_en_mux_sel              (sdr_tx_en_mux_sel)            ,
            .o_fcnt_no_frms_sel           (fcnt_no_frms_sel)         ,
            .o_tx_mode_mux_sel            (tx_mode_mux_sel)          ,
            .o_rx_en_mux_sel              (rx_en_mux_sel)            ,
            .o_rx_mode_mux_sel            (rx_mode_mux_sel)          ,
            .o_bit_cnt_en_mux_sel         (bit_cnt_en_mux_sel)       ,
            .o_bit_rx_cnt_en_mux_sel      (bit_rx_cnt_en_mux_sel)    ,
            .o_fcnt_en_mux_sel            (fcnt_en_mux_sel)          ,
            .o_ser_rx_tx_mux_sel             (ser_rx_tx_mux_sel)       ,
            .o_scl_idle_mux_sel           (scl_idle_mux_sel)         ,
            .o_bits_cnt_regf_rx_tx_sel (bits_cnt_regf_rx_tx_sel) ,
            .o_scl_stall_flag_sel      (sdr_scl_stall_flag_sel)      ,
            .o_scl_stall_cycles_sel    (sdr_scl_stall_cycles_sel)    ,
            //.o_scl_scl_gen_stall       (scl_gen_stall_sel),                 // 
            .o_controller_done            (o_ctrl_done)          ,
            ////////////////////////HDR///////////////////////////////
            .o_enthdr_en (enthdr_en),
            .o_mode_sda_sel  (sda_sel),
            .o_tx_en_sel (tx_en_sel),                                                                                        .o_hdrengine_en   (hdrengine_en), 
            .o_regf_wr_en_sdr_hdr_sel(regf_wr_en_mode), 
            .o_regf_data_sdr_hdr_sel (regf_data_mode),
            .o_regf_rd_en_sdr_hdr_sel(regf_rd_en_mode), 
            .o_regf_rd_address_sdr_hdr_sel(regf_rd_address_mode),
            .o_scl_pp_od_sdr_hdr_sel(scl_pp_od_mode),
            .o_scl_stall_flag_sdr_hdr_sel(scl_stall_flag_mux_sel),  //added
            .o_scl_stall_cycles_sdr_hdr_sel(scl_stall_cycles_mux_sel)      //added  
                                                );


sdr_mode u_sdr_mode (
            .i_sdr_ctrl_clk               (sys_clk_50mhz)            , //
            .i_sdr_ctrl_rst_n             (i_sdr_rst_n)              ,
            .i_sdr_ctrl_cnt_done          (sdr_ctrl_cnt_done)        ,
            .i_i3c_ctrl_sdr_en            (sdr_en)                   ,
            .i_sdr_ctrl_last_frame        (sdr_ctrl_last_frame)      ,
            .i_ser_mode_done              (ser_mode_done)            ,
            .i_deser_mode_done            (rx_mode_done)             ,
            .i_sdr_regf_rx_tx             (ser_rx_tx)                ,
            .i_ser_nack_ack               (ser_nack_ack)             ,
            .i_sdr_rx_rd_abort            (sdr_rx_rd_abort)          ,
            .i_ser_to_par_trans           (ser_to_parity_transition) ,
            .i_sdr_ctrl_bit_cnt_done      (sdr_ctrl_cnt_done)        ,
            .i_sdr_ctrl_scl_neg_edge      (scl_neg_edge)             ,
            .i_sdr_ctrl_scl_pos_edge      (scl_pos_edge)             ,
            .i_sdr_ctrl_scl_stall_done    (scl_pos_edge)             ,
            .i_sdr_rx_arbitration_lost    (rx_arbitration_lost)      ,
            .i_sdr_ctrl_ibi_payload_en    (sdr_ctrl_ibi_payload_en)  ,

            .o_sdr_ctrl_payload_done       (sdr_ibi_payload_done)  ,
            .o_sdr_ctrl_scl_stall_flag    (stall_flag)               ,
            .o_sdr_ctrl_scl_stall_cycles  (scl_stall_cycles)         ,
            .o_sdr_ctrl_scl_idle          (sdr_ctrl_scl_idle)        ,
            .o_sdr_ctrl_fcnt_en           (sdr_fcnt_en)              ,
            .o_sdr_ctrl_ser_en            (sdr_tx_en)                ,
            .o_sdr_ctrl_ser_valid         (sdr_ctrl_ser_valid)       ,
            .o_sdr_ctrl_ser_mode          (sdr_tx_mode)              ,
            .o_sdr_ctrl_deser_en          (sdr_rx_en)                ,
            .o_sdr_rx_mode                (sdr_rx_mode)              ,
            .o_sdr_ctrl_cnt_en            (sdr_bit_cnt_en)           ,
            .o_sdr_ctrl_rx_cnt_en         (sdr_bit_rx_cnt_en)        ,
            .o_sdr_ctrl_pp_od             (sdr_pp_od)                ,
            .o_sdr_ctrl_addr_done         (sdr_ctrl_addr_done)       ,
            .o_sdr_ctrl_done              (sdr_done)                 ,
            .o_sdr_ctrl_regf_wr_en        (regf_wr_en)               ,
            .o_sdr_ctrl_regf_rd_en_pulse  (sdr_regf_rd_en)           ,
            .o_sdr_ctrl_regf_addr         (sdr_regf_addr)            ,
            .o_sdr_ctrl_rx_valid          (sdr_rx_valid)            );

i2c_legacy_mode u_i2c_legacy_mode (
            .i_clk                        (sys_clk_50mhz)            ,
            .i_rst_n                      (i_sdr_rst_n)              ,
            .i_i2c_mode_en                (i2c_en)                   ,
            .i_last_frame                 (sdr_ctrl_last_frame)      ,
            .i_tx_mode_done               (ser_mode_done)            ,
            .i_rx_mode_done               (rx_mode_done)             ,
            .i_regf_rx_tx                 (ser_rx_tx)                ,
            .i_rx_nack_ack                (ser_nack_ack)             ,
            .i_scl_neg_edge               (scl_neg_edge)             ,
            .i_scl_pos_edge               (scl_pos_edge)             ,
            .i_rx_arbitration_lost        (rx_arbitration_lost)      ,
            .o_frame_cnt_en               (i2c_fcnt_en)              ,
            .o_bit_cnt_en                 (i2c_bit_cnt_en)           ,
            .o_bit_rx_cnt_en              (i2c_bit_rx_cnt_en)        ,
            .o_tx_en                      (i2c_tx_en)                ,
            .o_tx_mode                    (i2c_tx_mode)              ,
            .o_rx_en                      (i2c_rx_en)                ,
            .o_rx_mode                    (i2c_rx_mode)              ,
            .o_pp_od                      (i2c_pp_od)                ,
            .o_regf_rd_en                 (i2c_regf_rd_en)           ,
            .o_regf_addr                  (i2c_regf_addr)            ,
            .o_rx_data_valid              (i2c_rx_valid)             ,
            .o_target_nack                (target_nack)              ,
            .o_i2c_mode_done              (i2c_done)                );

dynamic_address_assignment  u_daa(
.i_daa_clk             (sys_clk_50mhz)            ,
.i_daa_rst_n           (i_sdr_rst_n)              ,
.i_mcu_daa_en          (daa_en)                   ,
.i_scl_daa_pos_edge    (scl_pos_edge)             ,
.i_scl_daa_neg_edge    (scl_neg_edge)             ,
.i_tx_daa_mode_done    (ser_mode_done)            ,
.i_tx_daa_done         (tx_daa_done)              ,
.i_rx_daa_mode_done    (rx_mode_done)             ,
.i_rx_daa_nack_ack     (ser_nack_ack)             ,
//.i_bits_cnt_daa_bit_cnt (sdr_cnt_bit_count)       ,
//.i_staller_daa_stall_done (scl_stall_done)        ,
.o_daa_pp_od           (daa_pp_od)                ,
.o_daa_regf_rd_en      (daa_regf_rd_en)           ,
.o_daa_regf_wr_en      (daa_regf_wr_en)           ,
.o_daa_regf_data_wr    (daa_regf_wr_data)         , ///// mux to be implemented
.o_daa_regf_addr       (daa_regf_addr)            ,
.o_daa_tx_mode         (daa_tx_mode)              ,
.o_daa_tx_en           (daa_tx_en)                ,
.o_daa_rx_mode         (daa_rx_mode)              ,
.o_daa_rx_en           (daa_rx_en)                ,
.o_daa_fcnt_en         (daa_fcnt_en)              ,
.o_daa_fcnt_no_frms    (daa_fcnt_no_frms)         ,
.o_daa_bits_cnt_en     (daa_bits_cnt_en)          ,
.o_daa_error           (daa_error)                ,
.o_regf_wr_data_mux_sel(regf_wr_data_mux_sel)     ,
.o_daa_rx_cnt_en       (daa_rx_cnt_en)            ,
//.o_daa_stall_flag      (daa_stall_flag)           ,
//.o_daa_stall_cycles    (daa_stall_cycles)         ,
.o_daa_mcu_done(daa_done)                        );

hot_join u_hot_join (
            .i_hot_join_clk               (sys_clk_50mhz)            ,
            .i_hot_join_rst_n             (i_sdr_rst_n)              ,
            .i_hot_join_enable            (hj_en)                    ,
            .i_hot_join_ccc               (hj_ccc)                   ,
            .i_hot_join_support           (hj_support_reg)           ,
            .i_hot_join_configuration     (hj_cfg_reg )              ,
            .i_hot_join_tx_mode_done      (ser_mode_done)            ,
            .i_hot_join_tx_pp_mode_done   (ser_pp_mode_done)         ,
            .i_hot_join_rx_mode_done      (rx_mode_done)             ,
            .i_hot_join_nack_ack          (ser_nack_ack)             ,
            .i_hot_join_scl_neg_edge      (scl_neg_edge)             ,
            .i_hot_join_scl_pos_edge      (scl_pos_edge)             ,
            .o_hot_join_tx_en             (hj_tx_en)                 ,
            .o_hot_join_tx_mode           (hj_tx_mode)               ,
            .o_hot_join_rx_en             (hj_rx_en)                 ,
            .o_hot_join_rx_mode           (hj_rx_mode)               ,
            .o_hot_join_regf_rd_en        (hj_regf_rd_en)            ,
            .o_hot_join_regf_addr         (hj_regf_addr)             ,
            .o_hot_join_cnt_en            (hj_bit_cnt_en)            ,
            .o_hot_join_pp_od             (hj_pp_od)                 ,
            .o_hot_join_daa_req           (hj_daa_req)               ,
            .o_hot_join_ctrl_role_pass    (hj_cr_pass)               ,
            .o_hot_join_acc_rej           (hj_acc_rej)               ,
            .o_hot_join_done              (hj_done)                 );


IBI  u_ibi (
    .i_ibi_clk             (sys_clk_50mhz),
    .i_ibi_rst_n            (i_sdr_rst_n),
    .i_ibi_en               (ibi_en) ,
    .i_ibi_scl_neg_edge     (scl_neg_edge) ,
    .i_ibi_scl_pos_edge     (scl_pos_edge) ,
    .i_ibi_bcr_reg          (regf_data_rd) ,
    .i_ibi_cfg_reg          (regf_ibi_cfg),
    .i_ibi_payload_size_reg (ibi_payload_size_reg),
    .i_ibi_tgt_address      (ibi_tgt_address) ,
    .i_ibi_ser_mode_done    (ser_mode_done),
    .i_ibi_scl              (scl),
    .i_ibi_rx_mode_done     (rx_mode_done) ,
    .i_ibi_payload_done     (sdr_ibi_payload_done) ,
    .i_ibi_ack_nack         (ser_nack_ack),

    .o_ibi_pp_od  (ibi_pp_od) ,
    .o_ibi_regf_address (ibi_regf_address),
    .o_ibi_regf_rd_en  ( ibi_regf_rd_en ),
    .o_ibi_rx_en      (ibi_rx_en),
    .o_ibi_tx_en      (ibi_tx_en),
    .o_ibi_regf_wr_en ( ibi_regf_wr_en ),
    .o_ibi_rx_mode    (ibi_rx_mode),
    .o_ibi_tx_mode    (ibi_tx_mode),
    .o_ibi_payload_en (ibi_payload_en),
    .o_ibi_cnt_en     (ibi_cnt_en),
    .o_ibi_ser_rx_tx  (ibi_ser_rx_tx) ,
    .o_ibi_done       (ibi_done)
   );

controller_crh u_controller_crh(
                  .i_crh_clk              (sys_clk_50mhz),
                  .i_crh_rst_n            (i_sdr_rst_n),
                  .i_crh_en               (crh_en),
                  .i_crh_initiated_request(hj_crh_en),
                  .i_crh_stop_is_sent     (crh_stop_is_sent),
                  .i_crh_CRHDLY           (crh_CRHDLY),
                  .i_crh_getstatus_data   (crh_getstatus_data),
                  .i_crh_CRCAP2           (crh_CRCAP2),
                  .i_crh_PRECR            (crh_PRECR),
                  .i_crh_cfg_reg          (crh_cfg_reg),
                  .i_crh_tgts_count       (crh_tgts_count),
                  .i_crh_tx_mode_done     (ser_mode_done),
                  .i_crh_tx_pp_mode_done  (ser_pp_mode_done),
                  .i_crh_sda_low          (crh_sda_low),
                  .i_crh_rx_mode_done     (rx_mode_done),
                  .i_crh_rx_pp_mode_done  (crh_rx_pp_mode_done),
                  .i_crh_rx_nack_ack      (ser_nack_ack),
                  .i_crh_scl_neg_edge     (scl_neg_edge),
                  .i_crh_scl_pos_edge     (scl_pos_edge),
                  .i_crh_start_detected   (crh_start_detected),
                  .i_crh_crhpoverlap      (timer_crhpol),
                  .i_crh_newcrlock        (timer_newcrlck_i3c),
                  .i_crh_timer_cas        (timer_cas),
                  .o_crh_tx_en            (crh_tx_en),
                  .o_crh_tx_mode          (crh_tx_mode),
                  .o_crh_rx_en            (crh_rx_en),
                  .o_crh_rx_mode          (crh_rx_mode),
                  .o_crh_regf_wr_en       (crh_regf_wr_en),
                  .o_crh_regf_rd_en       (crh_regf_rd_en),
                  .o_crh_regf_addr        (crh_regf_addr),
                  .o_crh_done             (crh_done)             ,
                  //.o_crh_ncr_win          (crh_ncr_win)          ,
                  //.o_crh_ncr_take_control (crh_ncr_take_control) ,
                  .o_crh_send_stop        (crh_send_stop),
                  .o_crh_pp_od            (crh_pp_od),
                  .o_crh_cnt_en           (crh_cnt_en),
                  .o_crh_rx_cnt_en        (crh_rx_cnt_en),
                  .o_crh_timer_set        (crh_timer_set),
                  .o_crh_timer_entasx     (crh_entasx),
                  .o_crh_fcnt_en          (crh_fcnt_en),
                  .o_crh_scl_idle         (crh_scl_idle)
);



i3c_timer_fsm u_i3c_timer (
            .i_clk                        (sys_clk_50mhz)            ,
            .i_rst_n                      (i_sdr_rst_n)              ,
            .i_start_pattern              (start_pattern)            ,
            .i_stop_pattern               (stop_pattern)             ,
            .i_chr_set                    (crh_timer_set)                     ,  // temp for tb till we do crhf
            .i_crh_entasx                 (crh_entasx)               ,
            .i_i3c_idle_flag              (i3c_idle_flag)            ,  // tbd
            .o_timer_cas                  (timer_cas)                ,
            .o_timer_bus_free_pure        (timer_bus_free_pure)      ,
            .o_timer_bus_free_mix_fm      (timer_bus_free_mix_fm)    ,
            .o_timer_bus_free_mix_fm_p    (timer_bus_free_mix_fm_p)  ,
            .o_timer_bus_aval             (timer_bus_aval)           ,
            .o_timer_bus_idle             (timer_bus_idle)           ,
            .o_timer_crhpol               (timer_crhpol)             ,
            .o_timer_newcrlck_i2c         (timer_newcrlck_i2c)       ,
            .o_timer_newcrlck_i3c         (timer_newcrlck_i3c)      );



controller_tx u_controller_tx (
            .i_clk                        (sys_clk_50mhz)            ,
            .i_rst_n                      (i_sdr_rst_n)              ,
            .i_ser_scl                    (scl)                      ,
            .i_ser_en                     (sdr_tx_en_mux_out)            ,
            .i_ser_valid                  (sdr_ctrl_ser_valid)       ,
            .i_ser_count                  (sdr_cnt_bit_count)        ,
            .i_ser_count_done             (sdr_ctrl_cnt_done)        ,
            .i_ser_mode                   (tx_mode_mux_out)          ,
            .i_ser_regf_data              (regf_data_rd)             ,
            .i_ser_scl_neg_edge           (scl_neg_edge)             , //cnflct from tx
            .i_ser_scl_pos_edge           (scl_pos_edge)             ,
            .i_timer_cas                  (timer_cas)                ,
            .i_timer_bus_free_pure         (timer_bus_free_pure)      , ////20244444444
            .o_ser_sda_low                (crh_sda_low)              ,
            .o_tx_daa_done                (tx_daa_done)              ,
            .o_stop_pattern               (stop_pattern)             ,
            .o_start_pattern              (start_pattern)            ,
            .o_ser_s_data                 (ser_s_data)               ,   // input to (sda_handling_mode_mux)
            .o_ser_mode_done              (ser_mode_done)            ,
            .o_ser_pp_mode_done           (ser_pp_mode_done)         ,
            .o_ser_to_parity_transition   (ser_to_parity_transition));

bits_counter_sdr u_bits_counter_sdr (
            .i_cnt_en                (bit_cnt_en_mux_out)    ,
            .i_ctrl_rx_cnt_en        (bit_rx_cnt_en_mux_out) ,
            .i_bits_cnt_clk          (sys_clk_50mhz)         ,
            .i_rst_n                 (i_sdr_rst_n)           ,
            .i_sdr_ctrl_pp_od        (scl_pp_od_mux_out)     ,
            .i_scl_pos_edge          (scl_pos_edge)          ,
            .i_scl_neg_edge          (scl_neg_edge )         ,
            .i_bits_cnt_regf_rx_tx   (bits_cnt_regf_rx_tx_mux_out)             ,
            .o_cnt_done              (sdr_ctrl_cnt_done)     ,
            .o_cnt_bit_count         (sdr_cnt_bit_count)    );

controller_rx u_controller_rx (
            .i_clk                        (sys_clk_50mhz)            ,
            .i_rst_n                      (i_sdr_rst_n)              ,
            .i_sdr_rx_scl                 (scl)                      ,
            .i_sdr_rx_en                  (rx_en_mux_out)            ,
            .i_sdr_rx_sda                 (deser_s_data)             ,
            .i_sdr_rx_des_count           (sdr_cnt_bit_count)        ,
            .i_sdr_rx_mode                (rx_mode_mux_out)          ,
            .i_fcnt_last_frame            (sdr_ctrl_last_frame)      ,
            .i_timer_cas                  (timer_cas)                ,
            .i_sdr_rx_scl_pos_edge           (scl_pos_edge)             ,
            .i_sdr_rx_tx_ser_data         (ser_s_data)               ,
            .o_crh_start_detected         (crh_start_detected)       ,
            .o_sdr_rx_nack_ack            (ser_nack_ack)             ,
            .o_sdr_rx_rd_abort            (sdr_rx_rd_abort)          , //to fsm
            .o_sdr_rx_regf_data_wr        (regf_data_wr)             ,
            .o_sdr_rx_mode_done           (rx_mode_done)             ,
            .o_sdr_rx_pp_mode_done        (crh_rx_pp_mode_done)      ,
            .o_sdr_rx_arbitration_lost    (rx_arbitration_lost)     );


frame_counter_sdr u_frame_counter_sdr (
            .i_fcnt_no_frms         (fcnt_no_frms_mux_out) ,
            .i_fcnt_clk             (sys_clk_50mhz)        ,
            .i_fcnt_rst_n           (i_sdr_rst_n)          ,
            .i_fcnt_en              (fcnt_en_mux_out)      ,
            .o_fcnt_last_frame      (sdr_ctrl_last_frame) );






sda_handling u_sda_handling (
            .i_handling_s_data            (ser_s_data_mux_out)               ,       //sda_handling_mode_mux output will repalced here
            .i_handling_sel_pp_od         (scl_pp_od_mux_out)        ,
            .i_handling_pp_en             (tx_en_mux_out)            , // same enable of the serializer //2024-edit to make it tx_en of hdr or sdr
            .o_handling_s_data            (deser_s_data)             ,
            .sda                          (sda)                     );

// SCL generation block for monitoring and stalling
scl_generation u_scl_generation (
            .i_sdr_ctrl_clk               (sys_clk_50mhz)            ,
            .i_sdr_ctrl_rst_n             (i_sdr_rst_n)              ,
            .i_sdr_scl_gen_pp_od          (scl_pp_od_mux_out)        ,
            .i_scl_gen_stall              (hdr_scl_stall_flag_mux_out),       // ADDED MUX OUT FOR STALLER (MAGH)  ,  //testing laila //(scl_gen_stall) 
            .i_sdr_ctrl_scl_idle          (sdr_scl_idle_mux_out )    ,
            .i_timer_cas                  (timer_cas)                ,
            .o_scl_pos_edge               (scl_pos_edge)             ,
            .o_scl_neg_edge               (scl_neg_edge)             ,
            .o_scl                        (scl)                     );


// SCL generation block for tx_hdr and rx_hdr that are never stalled
scl_generation u_scl_generation_not_stalled (
            .i_sdr_ctrl_clk               (sys_clk_50mhz)            ,
            .i_sdr_ctrl_rst_n             (i_sdr_rst_n)              ,
            .i_sdr_scl_gen_pp_od          (scl_pp_od_mux_out)        ,
            .i_scl_gen_stall              (1'b0)                     , 
            .i_sdr_ctrl_scl_idle          (sdr_scl_idle_mux_out )    ,
            .i_timer_cas                  (timer_cas)                ,
            .o_scl_pos_edge               (scl_pos_edge_not_stalled)             ,
            .o_scl_neg_edge               (scl_neg_edge_not_stalled)             ,
            .o_scl                        (scl_not_stalled)          );

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
            .o_ser_rx_tx                  (ser_rx_tx)                ,
            .o_regf_num_frames            (fcnt_no_frms)             ,
            .o_crh_CRHDLY                 (crh_CRHDLY)               ,
            .o_crh_getstatus_data         (crh_getstatus_data)       ,
            .o_crh_CRCAP2                 (crh_CRCAP2)               ,
            .o_crh_PRECR                  (crh_PRECR)                ,
            .o_crh_cfg_reg                (crh_cfg_reg)              ,
            .o_crh_tgts_count             (crh_tgts_count)           ,
            .o_regf_ibi_cfg                (regf_ibi_cfg)            ,
            .o_regf_ibi_payload_size_reg  (ibi_payload_size_reg)    ,
            .o_i_ibi_tgt_address          (ibi_tgt_address)         ,
            .o_regf_hj_cfg                (hj_cfg_reg)               ,
            .o_regf_hj_support            (hj_support_reg)          );

clk_divider u_clk_divider(
           .i_clk_in                      (i_sdr_clk)                ,
           .i_rst_n                       (i_sdr_rst_n)              ,
           .o_clk_out                     (sys_clk_50mhz)           );


////////////////////////////////////////// ENTHDR BLOCK ////////////////////////////////////////////
enthdr u_enthdr (
            .i_clk                          (sys_clk_50mhz)           ,
            .i_rst_n                        (i_sdr_rst_n)             ,
            .i_i3cengine_en                 (enthdr_en)               ,
            .i_tx_mode_done                 (ser_mode_done)           ,
            .i_rx_ack_nack                  (ser_nack_ack)            ,
            .i_scl_neg_edge                 (scl_neg_edge)            ,
            .i_scl_pos_edge                 (scl_pos_edge)            ,
            .i_rx_mode_done                 (rx_mode_done)            ,
            .o_bit_cnt_en                   (enthdr_bit_cnt_en)       ,
            .o_pp_od                        (enthdr_pp_od)            ,
            .o_regf_rd_en                   (enthdr_regf_rd_en)       ,
            .o_regf_addr                    (enthdr_regf_addr)        ,
            .o_tx_en                        (enthdr_tx_en)            ,
            .o_tx_mode                      (enthdr_tx_mode)          ,
            .o_rx_en                        (enthdr_rx_en)            ,
            .o_rx_mode                      (enthdr_rx_mode)          ,
            .o_i3cengine_done               (enthdr_done)             
);


hdr_engine u_hdr_engine (
    .i_sys_clk                              (sys_clk_50mhz)           , 
    .i_sys_rst_n                            (i_sdr_rst_n)             ,
        .i_i3cengine_hdrengine_en           (hdrengine_en)            , 
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
/*
    .o_int_regf_Dummy_conf          (o_int_regf_Dummy_conf),
    .o_regf_addr_special                    (engine_configuration_addr)    );
*/
    .o_regf_addr_special                    (engine_configuration_addr) ,
    .o_crc_rx_tx_mux_sel_ccc_nt_sel          (crc_rx_tx_mux_sel_ccc_nt_sel)   );

     //output  reg   [7:0]     o_regf_addr_special






gen_mux #(1,3) regf_rd_en_mux (
            .data_in  ({ enthdr_regf_rd_en, crh_regf_rd_en , ibi_regf_rd_en , hj_regf_rd_en , daa_regf_rd_en , i3c_regf_rd_en , i2c_regf_rd_en , sdr_regf_rd_en}),
            .ctrl_sel (regf_rd_en_mux_sel)  ,
            .data_out (regf_rd_en_sdr_mux_out) );

gen_mux #(12,3) regf_rd_address_mux (
            .data_in  ({ enthdr_regf_addr, crh_regf_addr , ibi_regf_address , hj_regf_addr , daa_regf_addr , 12'b0 , i2c_regf_addr , sdr_regf_addr}),
            .ctrl_sel (regf_rd_address_mux_sel)  ,
            .data_out (regf_rd_address_sdr_mux_out) );

gen_mux #(1,3) regf_wr_en_mux (
            .data_in  ({ 1'b0, crh_regf_wr_en , ibi_regf_wr_en , 1'b0 , daa_regf_wr_en , i3c_rx_valid , i2c_rx_valid , sdr_rx_valid}),
            .ctrl_sel (regf_wr_en_mux_sel)  ,
            .data_out (regf_wr_en_sdr_mux_out) );

gen_mux #(8,1) regf_wr_data_mux (
            .data_in  ({daa_regf_wr_data , regf_data_wr}),
            .ctrl_sel (regf_wr_data_mux_sel)  ,
            .data_out (regf_wr_data_sdr_mux_out) );

gen_mux #(1,3) scl_pp_od_mux (
            .data_in  ({ enthdr_pp_od, crh_pp_od , ibi_pp_od , hj_pp_od , daa_pp_od ,i3c_pp_od , i2c_pp_od , sdr_pp_od}),
            .ctrl_sel (scl_pp_od_mux_sel)  ,
            .data_out (scl_pp_od_sdr_mux_out) );

///// to be removed /////
gen_mux #(1,3) scl_idle_mux (
            .data_in  ({ 1'b0, crh_scl_idle ,1'b0 ,1'b0 , 1'b0 , i3c_scl_idle , 1'b0 , sdr_ctrl_scl_idle}),
            .ctrl_sel (scl_idle_mux_sel)      ,
            .data_out (sdr_scl_idle_mux_out) );

gen_mux #(1,3) tx_en_mux (
            .data_in  ({ enthdr_tx_en, crh_tx_en, ibi_tx_en , hj_tx_en , daa_tx_en , i3c_tx_en , i2c_tx_en , sdr_tx_en}),
            .ctrl_sel (sdr_tx_en_mux_sel)  ,
            .data_out (sdr_tx_en_mux_out) );

gen_mux #(3,3) tx_mode_mux (
            .data_in  ({ enthdr_tx_mode, crh_tx_mode,ibi_tx_mode ,hj_tx_mode , daa_tx_mode , i3c_tx_mode , i2c_tx_mode , sdr_tx_mode}),
            .ctrl_sel (tx_mode_mux_sel)  ,
            .data_out (tx_mode_mux_out) );

gen_mux #(1,3) rx_en_mux (
            .data_in  ({ enthdr_rx_en, crh_rx_en ,ibi_rx_en , hj_rx_en , daa_rx_en , 1'b0 , i2c_rx_en , sdr_rx_en}),
            .ctrl_sel (rx_en_mux_sel)  ,
            .data_out (rx_en_mux_out) );

gen_mux #(3,3) rx_mode_mux (
            .data_in  ({ enthdr_rx_mode, crh_rx_mode , ibi_rx_mode , hj_rx_mode , daa_rx_mode , 3'b00 , i2c_rx_mode , sdr_rx_mode}),
            .ctrl_sel (rx_mode_mux_sel)  ,
            .data_out (rx_mode_mux_out) );

gen_mux #(1,3) bit_cnt_en_mux (
            .data_in  ({enthdr_bit_cnt_en, crh_cnt_en , ibi_cnt_en , hj_bit_cnt_en , daa_bits_cnt_en , i3c_bit_cnt_en , i2c_bit_cnt_en , sdr_bit_cnt_en}),
            .ctrl_sel (bit_cnt_en_mux_sel)  ,
            .data_out (bit_cnt_en_mux_out) );


gen_mux #(1,3) bit_rx_cnt_en_mux (
            .data_in  ({ 1'b0, crh_rx_cnt_en, 1'b0 , 1'b0 , daa_rx_cnt_en , 1'b0 , i2c_bit_rx_cnt_en , sdr_bit_rx_cnt_en}),
            .ctrl_sel (bit_rx_cnt_en_mux_sel)  ,
            .data_out (bit_rx_cnt_en_mux_out) );

gen_mux #(1,3) fcnt_en_mux (
            .data_in  ({1'b0, crh_fcnt_en , 1'b0 , 1'b0 , daa_fcnt_en , 1'b0 , i2c_fcnt_en , sdr_fcnt_en}),
            .ctrl_sel (fcnt_en_mux_sel)  ,
            .data_out (fcnt_en_mux_out) );

gen_mux #(8,3) fcnt_no_frms_mux (
            .data_in  ({ 8'b0 ,ibi_payload_size_reg , 8'b0 , daa_fcnt_no_frms , fcnt_no_frms , fcnt_no_frms , fcnt_no_frms}),
            .ctrl_sel (fcnt_no_frms_sel)      ,
            .data_out (fcnt_no_frms_mux_out) );

gen_mux #(1,3) bits_cnt_regf_rx_tx_mux (
            .data_in  ( { ser_rx_tx , ser_rx_tx ,  ser_rx_tx ,  1'b1 , ser_rx_tx , ser_rx_tx , ser_rx_tx} ),
            .ctrl_sel (bits_cnt_regf_rx_tx_sel)         ,
            .data_out (bits_cnt_regf_rx_tx_mux_out) )   ;

gen_mux #(1,3) scl_stall_flag_mux (
            .data_in  ( {stall_flag , stall_flag , stall_flag , daa_stall_flag , stall_flag , stall_flag , stall_flag , stall_flag} ),
            .ctrl_sel (sdr_scl_stall_flag_sel)         ,
            .data_out (sdr_scl_stall_flag_mux_out) )   ;

gen_mux #(5,3) scl_stall_cycles_mux (
            .data_in  ( { scl_stall_cycles ,  scl_stall_cycles ,  scl_stall_cycles , daa_stall_cycles , scl_stall_cycles , scl_stall_cycles , scl_stall_cycles} ),
            .ctrl_sel (sdr_scl_stall_cycles_sel)         ,
            .data_out (sdr_scl_stall_cycles_mux_out) )   ;


gen_mux #(1,3) u_fcnt_en_mux (
            .data_in  ({ ser_rx_tx, ser_rx_tx, ibi_ser_rx_tx, ser_rx_tx, ser_rx_tx , ser_rx_tx ,ser_rx_tx , ser_rx_tx}),
            .ctrl_sel (ser_rx_tx_mux_sel)  ,
            .data_out (ser_rx_tx_bits_count_mux_out) );




///This MUX used to choose which mode (HDR OR SDR) Control the SDA Line
gen_mux #(1,1) sda_handling_mode_mux (
            .data_in  ({ser_hdr_data,ser_s_data}),        
            .ctrl_sel (sda_sel)  ,
            .data_out (ser_s_data_mux_out) );

//////////////////hdr_mux/////////////////////




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

gen_mux #(3,1) rx_mode_hdr_mux (
            .data_in  ({ccc_rx_mode, ddr_rx_mode}),             
            .ctrl_sel (hdr_rx_mode_sel)  ,
            .data_out (rx_mode_hdr_mux_out) );



 /*gen_mux #(1,1) pp_od_hdr_mux (
            .data_in  ({ccc_pp_od, ddr_pp_od}),             ////to be added out from ccc/ddr blocks
            .ctrl_sel (hdr_sdahand_pp_od_sel)  ,
            .data_out (scl_pp_od_hdr_mux_out) ); */

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



///////////////sdr_hdr_muxs/////////////////////


gen_mux #(5,1) scl_stall_cycles_mode_mux (
            .data_in  ({hdr_scl_stall_cycles_mux_out,sdr_scl_stall_cycles_mux_out}),        
            .ctrl_sel (scl_stall_cycles_mux_sel)  ,
            .data_out (scl_stall_cycles_mux_out));

gen_mux #(1,1) scl_stall_flag_mode_mux (
            .data_in  ({hdr_scl_stall_flag_mux_out,sdr_scl_stall_flag_mux_out}),        
            .ctrl_sel (scl_stall_flag_mux_sel)  ,
            .data_out (scl_stall_flag_mux_out));


gen_mux #(1,1) reg_rd_en_mode_mux (
            .data_in  ({regf_rd_en_hdr_mux_out,regf_rd_en_sdr_mux_out}),        
            .ctrl_sel (regf_rd_en_mode)  ,
            .data_out (regf_rd_en_mode_mux_out));

gen_mux #(1,1) reg_wr_en_mode_mux (
            .data_in  ({regf_wr_en_hdr_mux_out,regf_wr_en_sdr_mux_out}),        
            .ctrl_sel (regf_wr_en_mode)  ,
            .data_out (regf_wr_en_mode_mux_out));


gen_mux #(12,1) regf_rd_address_mode_mux (
            .data_in  ({ regf_rd_address_hdr_mux_out,regf_rd_address_sdr_mux_out }),
            .ctrl_sel (regf_rd_address_mode)  ,
            .data_out (regf_rd_address_mode_mux_out) );

gen_mux #(8,1) regf_wr_data_mode_mux (
            .data_in  ({regfcrc_rx_data_out , regf_wr_data_sdr_mux_out}),
            .ctrl_sel (regf_data_mode)  ,
            .data_out (regf_wr_data_mode_mux_out) );

gen_mux #(1,1) scl_pp_od_mode_mux (
            .data_in ({scl_pp_od_hdr_mux_out,scl_pp_od_sdr_mux_out}),
            .ctrl_sel (scl_pp_od_mode),
            .data_out (scl_pp_od_mux_out)
    );


// to choose which tx enable signal will be input to sda handling
gen_mux #(1,1) tx_en_mode_mux (
            .data_in  ({tx_en_hdr_mux_out, sdr_tx_en_mux_out}),             
            .ctrl_sel (tx_en_sel)  ,
            .data_out (tx_en_mux_out) );


//////////////reg_file(Config /data write)///////////////////

gen_mux #(1,1) reg_wr_en_config_data_mux (
            .data_in  ({i_regf_wr_en_config,regf_wr_en_mode_mux_out}),        
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_wr_en_mux_out));


gen_mux #(12,1) regf_rd_address_config_data_mux (
            .data_in  ({i_regf_wr_address_config,regf_rd_address_mode_mux_out}),
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_rd_address_mux_out) );

gen_mux #(8,1) regf_wr_data_config_data_mux (
            .data_in  ({i_regf_config , regf_wr_data_mode_mux_out}),
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_wr_data_mux_out) );


gen_mux #(1,1) reg_rd_en_config_data_mux (
            .data_in  ({i_regf_rd_en_config,regf_rd_en_mode_mux_out}),        
            .ctrl_sel (i_data_config_mux_sel)  ,
            .data_out (regf_rd_en_mux_out));






    // DUT instantiation
     
    CCC_Handler CCC_Handler (
        .i_sys_clk              (sys_clk_50mhz),
        .i_sys_rst              (i_sdr_rst_n),
        .i_engine_en            (engine_ccc_enable),
        .i_bitcnt_number        (cnt_bit_count),
        .i_tx_mode_done         (tx_hdr_mode_done),
        .i_rx_mode_done         (rx_hdr_mode_done),
        .i_rx_pre               (rx_pre),
        .i_sclstall_stall_done  (scl_stall_done),
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
        .o_engine_odd           (engine_odd),
        .o_regf_ERR_STATUS       (o_regf_ERR_STATUS_tb),    //??? not an input to regfile - yes it's output to the interface (response fifo or testbench)
        .o_crc_rx_tx_mux_sel_ccc (crc_rx_tx_mux_sel_ccc)
        /*.o_crc_en_rx_tx_mux_sel(crc_en_rx_tx_mux_sel),
        .o_crc_data_rx_tx_valid_sel(crc_data_rx_tx_valid_sel),
        .o_crc_data_tx_rx_mux_sel(crc_data_tx_rx_mux_sel),
        .o_crc_last_byte_tx_rx_mux_sel(crc_last_byte_tx_rx_mux_sel*/    
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
   
        .i_staller_done(scl_stall_done),
        .o_sclstall_no_of_cycles(ddr_scl_stall_cycles),  
        .o_sclstall_en(ddr_scl_stall_en),
    
        .o_regf_abort(o_regf_abort),
        .o_regf_error_type(o_regf_error_type),  
        .o_regf_wr_en(ddr_regf_wr_en),
        .o_regf_rd_en(ddr_regf_rd_en), // done
        .o_regf_addr(ddr_regf_addr),
        .o_engine_done(ddr_engine_done),
        /*.o_crc_en_rx_tx_mux_sel(crc_en_rx_tx_mux_sel),
        .o_crc_data_rx_tx_valid_sel(crc_data_rx_tx_valid_sel),
        .o_crc_data_tx_rx_mux_sel(crc_data_tx_rx_mux_sel),
        .o_crc_last_byte_tx_rx_mux_sel(crc_last_byte_tx_rx_mux_sel)*/
        .o_crc_rx_tx_mux_sel_NT(crc_rx_tx_mux_sel_NT)
    );



// sdr staller
scl_staller u_scl_staller(
.i_stall_clk(sys_clk_50mhz),
.i_stall_rst_n(i_sdr_rst_n),
.i_stall_flag(scl_stall_flag_mux_out),
.i_stall_cycles(scl_stall_cycles_mux_out),
.o_stall_done(scl_stall_done),
.o_scl_stall (scl_gen_stall) );

// hdr staller 

/*    scl_staller scl_staller_hdr (
         .i_stall_clk(sys_clk_50mhz), 
         .i_stall_rst_n(i_sdr_rst_n),
         .i_stall_flag(hdr_scl_stall_en_mux_out),
         .i_stall_cycles(hdr_scl_stall_cycles_mux_out),
         .o_stall_done(scl_stall_done_hdr),
         .o_scl_stall(o_scl_stall_hdr)
    ); */


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


wire tx_crc_last_byte;
wire rx_crc_last_byte;

        RX RX (
        .i_sys_clk                  (sys_clk_50mhz)               ,
        .i_sys_rst                  (i_sdr_rst_n)             ,
        .i_sclgen_scl               (scl_not_stalled)                   ,
        .i_sclgen_scl_pos_edge      (scl_pos_edge_not_stalled)           ,
        .i_sclgen_scl_neg_edge      (scl_neg_edge_not_stalled)           ,
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
        .o_crc_en                   (rx_crc_en)               , // 
        .o_crc_data_valid           (rx_crc_data_valid),
        .o_crc_last_byte            (rx_crc_last_byte)

        );

        tx tx (
        .i_sys_clk               (sys_clk_50mhz),
        .i_sys_rst               (i_sdr_rst_n),
        .i_ddrccc_tx_en          (tx_en_hdr_mux_out),
        .i_sclgen_scl_pos_edge   (scl_pos_edge_not_stalled),
        .i_sclgen_scl_neg_edge   (scl_neg_edge_not_stalled),
        .i_ddrccc_tx_mode        (tx_mode_hdr_mux_out),
        .i_regf_tx_parallel_data (regf_data_rd),
        .i_ddrccc_special_data   (cccnt_tx_special_data_mux_out), 
        .i_crc_crc_value         (crc_value),
        .i_crc_data_valid        (crc_valid), // added recently
        .i_regf_read_n_write_bit (cccnt_RnW), // added recently  -- not sure of this connection
        .o_sdahnd_serial_data    (ser_hdr_data),
        .o_ddrccc_mode_done      (tx_hdr_mode_done),
        .o_crc_parallel_data     (tx_crc_parallel_data),
        .o_crc_en                (tx_crc_en),
        .o_crc_last_byte         (tx_crc_last_byte),
        .o_crc_data_valid        (tx_crc_data_valid)
        );




  



crc u_crc (
            .i_sys_clk(sys_clk_50mhz),
            .i_sys_rst(i_sdr_rst_n),
            .i_txrx_en(crc_en_mux_out),   // mux to be an input either from tx or rx
            .i_txrx_data_valid(crc_data_valid_mux_out), // mux to be an input either from tx or rx
            .i_txrx_last_byte(crc_last_byte_mux_out), // mux to be an input either from tx or rx
            .i_txrx_data(crc_data_mux_out), // mux to be an input either from tx or rx
            .o_txrx_crc_value(crc_value), // mux to be an input either from tx or rx
            .o_txrx_crc_valid(crc_valid) // mux to be an input either from tx or rx
);



/*gen_mux #(1,1) crc_en_ddr_ccc_sel_mux (
            .data_in  ({ccc_crc_en,ddr_crc_en}),   
            .ctrl_sel (crc_en_ccc_ddr_mux_sel)  ,
            .data_out (crc_en_rx_tx_mux_sel));*/







gen_mux #(1,1) crc_en_tx_rx_mux (
            .data_in  ({rx_crc_en,tx_crc_en}),   //0:tx ---------//1:rx     
            .ctrl_sel (crc_rx_tx_mux_sel_ccc_nt_out)  ,
            .data_out (crc_en_mux_out));



gen_mux #(1,1) crc_data_tx_rx_valid (
            .data_in  ({rx_crc_data_valid,tx_crc_data_valid}),   //0:tx ---------//1:rx     
            .ctrl_sel (crc_rx_tx_mux_sel_ccc_nt_out)  ,
            .data_out (crc_data_valid_mux_out));



gen_mux #(8,1) crc_tx_rx_data_in (
            .data_in  ({regfcrc_rx_data_out , tx_crc_parallel_data}),
            .ctrl_sel (crc_rx_tx_mux_sel_ccc_nt_out)  ,
            .data_out (crc_data_mux_out) );



gen_mux #(1,1) crc_last_byte_tx_rx (
            .data_in  ({rx_crc_last_byte,tx_crc_last_byte}),   //0:tx ---------//1:rx     
            .ctrl_sel (crc_rx_tx_mux_sel_ccc_nt_out) ,
            .data_out (crc_last_byte_mux_out));


gen_mux #(1,1) crc_tx_rx_nt_CCC_sel (
            .data_in  ({crc_rx_tx_mux_sel_ccc, crc_rx_tx_mux_sel_NT}),             
            .ctrl_sel (crc_rx_tx_mux_sel_ccc_nt_sel)  ,
            .data_out (crc_rx_tx_mux_sel_ccc_nt_out) );


//draft
/*
        mux  #(.WIDTH(1)) mux_1 (
            .i_mux_one(my_regf_wr_en_tb),
            .i_mux_zero(o_regf_wr_en_tb),
            .i_selector(my_regf_wr_en_tb_selector),
            .o_mux_out(my_regf_wr_en_tb_mux_out)
            );

        mux #(.WIDTH(8)) mux_2  (
            .i_mux_one(my_regf_data_wr_tb),
            .i_mux_zero(i_regf_data_wr_tb),
            .i_selector(my_regf_data_wr_tb_selector),
            .o_mux_out(my_regf_data_wr_tb_mux_out)
            );

        mux  #(.WIDTH(12)) mux_3 (
            .i_mux_one(my_regf_addr_tb),
            .i_mux_zero(o_regf_addr_tb),
            .i_selector(my_regf_addr_tb_selector),
            .o_mux_out(my_regf_addr_tb_mux_out)
            );

*/
/*
         //////////////////////////////////////// for testing only /////////////////////////////////////////// 
         reg          my_regf_wr_en_tb ;
         reg          my_regf_wr_en_tb_selector ;
         wire         my_regf_wr_en_tb_mux_out ;

         reg  [7:0]   my_regf_data_wr_tb ;
         reg          my_regf_data_wr_tb_selector ;
         wire [7:0]   my_regf_data_wr_tb_mux_out ;

         reg  [11:0]  my_regf_addr_tb ;
         reg          my_regf_addr_tb_selector ;
         wire [11:0]  my_regf_addr_tb_mux_out ;
*/
/*         
         reg_file reg_file (
        .i_regf_clk(sys_clk_50mhz),
        .i_regf_rst_n(rst_n),
        .i_regf_rd_en(o_regf_rd_en_tb),
        .i_regf_wr_en(my_regf_wr_en_tb_mux_out),            // muxed 
        .i_regf_data_wr(my_regf_data_wr_tb_mux_out),        // muxed with rx 
        .i_regf_addr(my_regf_addr_tb_mux_out),              // muxed 
        .i_engine_configuration(i_engine_configuration_tb),

        .o_frmcnt_data_len(i_regf_DATA_LEN_tb),
        .o_cccnt_CMD_ATTR(i_regf_CMD_ATTR_tb),
        .o_engine_TID(o_engine_TID_tb),
        .o_ccc_CMD(i_regf_CMD_tb),
        .o_cccnt_DEV_INDEX(i_regf_DEV_INDEX_tb),
        .o_frmcnt_DTT(i_regf_DTT_tb),
        .o_engine_MODE(o_engine_MODE_tb), // with engine 
        .o_cccnt_RnW(i_regf_RnW_tb),
        .o_cccnt_WROC(i_regf_WROC_tb),
        .o_cccnt_TOC(i_regf_TOC_tb),
        .o_cccnt_DBP(i_regf_DBP_tb),
        .o_cccnt_SRE(i_regf_SRE_tb),
        .o_engine_CP(o_engine_CP_tb),

        .o_ser_rx_tx(),
        .o_regf_data_rd(i_regf_tx_parallel_data_tb),
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
*/

/*
         wire [7:0]  i_regf_data_wr_tb ;
         reg  [11:0] i_engine_configuration_tb ;
         wire [3:0]  o_engine_TID_tb ;
         wire [2:0]  o_engine_MODE_tb ;
         wire        o_engine_CP_tb ;
         wire [7:0]  i_regf_tx_parallel_data_tb ;
*/

        //wire o_scl_stall_tb ; // mesh mohem at the moment
         
    

    /*
    // related to regfile (configuration)
    wire        i_regf_RnW_tb ,i_regf_TOC_tb , i_regf_WROC_tb , i_regf_DBP_tb , i_regf_SRE_tb ;
    wire [2:0]  i_regf_CMD_ATTR_tb ;
    wire [7:0]  i_regf_CMD_tb ;
    wire [4:0]  i_regf_DEV_INDEX_tb ;
    wire [2:0]  i_regf_DTT_tb ;
    wire        o_regf_wr_en_tb , o_regf_rd_en_tb ;
    wire [11:0] o_regf_addr_tb ;            // this may be changed 
    wire        ccc_engine_done ;
    */

endmodule
`default_nettype wire
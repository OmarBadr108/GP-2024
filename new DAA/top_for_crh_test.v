//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors: MOSTAFA HASSAN 
// Revision: 
//
// Version : 1.0
//
// Create Date:  20:54:44 18/4/2023 
// Design Name:  top_for_crh_test
// Module Name:  top_for_crh_test 
//
//==================================================================================
//
//  STATEMENT OF USE
//
//  This information contains confidential and proprietary information of MIXEL.
//  No part of this information may be reproduced, transmitted, transcribed,
//  stored in a retrieval system, or translated into any human or computer
//  language, in any form or by any means, electronic, mechanical, magnetic,
//  optical, chemical, manual, or otherwise, without the prior written permission
//  of MIXEL.  This information was prepared for Garduation Project purpose and is for
//  use by MIXEL Engineers only.  MIXEL and ASU 2023 GP reserves the right 
//  to make changes in the information at any time and without notice.
//
//==================================================================================
//////////////////////////////////////////////////////////////////////////////////
`timescale 1ns / 1ps

`default_nettype none

module top_for_crh_test (
    input  wire          i_sdr_clk           , // system clk
    input  wire          i_sdr_rst_n         , // asynch neg edge reset 
    //input  wire          i_i3c_ctrl_sdr_en   , // sdr block enable signal 
    inout  wire          sda                 , // sda bus
    output wire          scl                 , // scl bus   
    output wire          o_sdr_rx_valid      , // output to host >> valid data are loaded
    output wire          o_sdr_ctrl_done     ,
    //inputs for testing
    input  wire              i_crh_en,
    input  wire  [7:0]       i_crh_CRHDLY,
    input  wire  [7:0]       i_crh_getstatus_data,
    input  wire  [7:0]       i_crh_CRCAP2,
    input  wire  [7:0]       i_crh_PRECR,
    input  wire  [7:0]       i_crh_cfg_reg,
    input  wire  [7:0]       i_crh_tgts_count,
    
    input  wire              i_crh_crhpoverlap,
    input  wire              i_crh_newcrlock,
    input  wire              i_crh_timer_cas,
    //outputs for testing
    output  wire              o_crh_done,
    output  wire              o_crh_ncr_win,
    output  wire              o_crh_ncr_take_control
    
    
    
    );  


//-- top module wires 

///////////////////// bits_counter wires /////////////////////////
    wire                 sdr_cnt_en                ;
    wire                 sdr_ctrl_rx_cnt_en        ;
    wire                 sdr_ctrl_cnt_done         ;
    wire         [2:0]   sdr_cnt_bit_count         ;
    wire                 sdr_ctrl_addr_done        ;

///////////////////////  sdr_tx wires   ///////////////////////////
    wire                 sdr_ctrl_ser_en           ;
    wire                 sdr_ctrl_ser_valid        ;
    wire         [2:0]   sdr_ctrl_ser_mode         ;
    wire                 ser_s_data                ;
    wire                 ser_mode_done             ;
    wire                 ser_to_parity_transition  ;

///////////////////////  sdr_rx wires   ///////////////////////////
    wire                 sdr_ctrl_deser_en         ;
    wire                 deser_s_data              ;
    wire         [1:0]   sdr_rx_mode               ;
    wire                 ser_nack_ack              ;
    wire                 sdr_rx_rd_abort           ;  
    wire                 rx_mode_done              ;

/////////////////////  frame_counter wires   ///////////////////////
    wire      [7:0]      fcnt_no_frms              ;
    wire                 sdr_ctrl_fcnt_en          ;
    wire                 sdr_ctrl_last_frame       ;

/////////////////  sda_handling/scl_gen wires   ///////////////////    
    wire                 sdr_ctrl_pp_od            ;
    wire                 scl_pos_edge              ;
    wire                 scl_neg_edge              ;
    wire                 scl_gen_stall             ; 
    wire                 stall_flag                ;  
    wire      [3:0]      scl_stall_cycles          ;
    wire                 scl_stall_done            ;
    wire                 sdr_ctrl_scl_idle         ;

/////////////////////  reg_file wires   ///////////////////////////           
    wire                 regf_rd_en                ;
    wire                 regf_wr_en                ;
    wire      [8:0]      regf_addr                 ;
    wire      [7:0]      regf_data_wr              ;
    wire      [7:0]      regf_data_rd              ;
    wire                 ser_rx_tx                 ;
    wire                 sdr_rx_valid              ;  
/////////////////////  controller_crh wires   ///////////////////////////
    wire                 start_detected            ; 
    wire                 sda_low                   ;
    wire                 last_bit                  ;
    wire  [7:0]          CRHDLY                    ;
    wire  [7:0]          getstatus_data            ;
    wire  [7:0]          CRCAP2                    ;
    wire  [7:0]          PRECR                     ;
    wire  [7:0]          cfg_reg                   ;
    wire  [7:0]          tgts_count                ;
    wire                 timer_set                 ;
    wire  [1:0]          timer_entasx              ;
    wire                 start_pattern             ;
    wire                 stop_pattern              ;
    wire                 ser_pp_mode_done          ;
    wire                 tx_daa_done               ;
    wire                 rx_pp_mode_done           ;
    
    wire i_i3c_ctrl_sdr_en 						   ;

assign i_i3c_ctrl_sdr_en = (i_crh_en)? 0 : 1 ;
assign o_sdr_rx_valid = sdr_rx_valid ;            
   
controller_crh u_controller_crh (
            .i_crh_clk               (i_sdr_clk)             ,
            .i_crh_rst_n             (i_sdr_rst_n)           ,
            .i_crh_en                (i_crh_en)              ,
            .i_crh_CRHDLY            (CRHDLY)                ,
            .i_crh_getstatus_data    (getstatus_data)        ,
            .i_crh_CRCAP2            (CRCAP2)                ,
            .i_crh_PRECR             (PRECR)                 ,
            .i_crh_cfg_reg           (cfg_reg)               ,
            .i_crh_tgts_count        (tgts_count)            ,
            .i_crh_tx_mode_done      (ser_mode_done)         ,
            .i_crh_tx_pp_mode_done   (ser_pp_mode_done)      ,
            .i_crh_sda_low           (sda_low)               ,
            .i_crh_rx_mode_done      (rx_mode_done)          ,
            .i_crh_rx_pp_mode_done   (rx_pp_mode_done)       ,
            .i_crh_rx_nack_ack       (ser_nack_ack)          ,
            .i_crh_scl_neg_edge      (scl_neg_edge)          ,
            .i_crh_scl_pos_edge      (scl_pos_edge)          ,
            .i_crh_start_detected    (start_detected)        ,
            .i_crh_last_bit_flag     (last_bit)              ,
            .i_crh_crhpoverlap       (i_crh_crhpoverlap)     ,
            .i_crh_newcrlock         (i_crh_newcrlock)       ,
            .i_crh_timer_cas         (i_crh_timer_cas)       ,
            .o_crh_tx_en             (sdr_ctrl_ser_en)       ,
            .o_crh_tx_mode           (sdr_ctrl_ser_mode)     ,
            .o_crh_rx_en             (sdr_ctrl_deser_en)     ,
            .o_crh_rx_mode           (sdr_rx_mode)           ,
			      .o_crh_regf_wr_en        (regf_wr_en)			         ,
			      .o_crh_regf_rd_en		      (regf_rd_en)			         ,
			      .o_crh_regf_addr		       (regf_addr)			          ,
            .o_crh_done              (o_crh_done)            ,
            .o_crh_ncr_win           (o_crh_ncr_win)         ,
            .o_crh_ncr_take_control  (o_crh_ncr_take_control),
            .o_crh_pp_od             (sdr_ctrl_pp_od)        ,
            .o_crh_cnt_en            (sdr_cnt_en)            ,
            .o_crh_rx_cnt_en         (sdr_ctrl_rx_cnt_en)    ,
            .o_crh_timer_set         (timer_set)             ,
            .o_crh_timer_entasx      (timer_entasx)          ,
            .o_crh_fcnt_en           (sdr_ctrl_fcnt_en)      ,
            .o_crh_scl_idle          (sdr_ctrl_scl_idle)     );     
          
               
bits_counter u_bits_counter ( 
            .i_cnt_en                (sdr_cnt_en)          ,
            .i_ctrl_rx_cnt_en        (sdr_ctrl_rx_cnt_en)  ,  
            .i_bits_cnt_clk          (i_sdr_clk)           ,
            .i_rst_n                 (i_sdr_rst_n)         ,
            .i_sdr_ctrl_pp_od        (sdr_ctrl_pp_od)      ,             
            .i_scl_pos_edge          (scl_pos_edge)        ,
            .i_scl_neg_edge          (scl_neg_edge )       ,
            .i_bits_cnt_regf_rx_tx   (ser_rx_tx)           ,
            .o_cnt_done              (sdr_ctrl_cnt_done)   , 
            .o_cnt_bit_count         (sdr_cnt_bit_count)  ); 


controller_RX u_controller_rx (
              .i_clk                   (i_sdr_clk)                 ,                
              .i_rst_n                 (i_sdr_rst_n)               ,
              .i_sdr_rx_scl            (scl)                       ,
              .i_sdr_rx_en             (sdr_ctrl_deser_en)         ,
              .i_sdr_rx_sda            (deser_s_data)              ,
              .i_sdr_rx_des_count      (sdr_cnt_bit_count)         ,
              .i_sdr_rx_count_done     (sdr_ctrl_cnt_done)          ,
              .i_sdr_rx_mode           (sdr_rx_mode)               ,
              .i_fcnt_last_frame       (sdr_ctrl_last_frame)       ,
              .i_timer_cas             (i_crh_timer_cas)           ,
              .i_sdr_rx_scl_neg_edge   (scl_neg_edge)              ,
              .i_sdr_rx_scl_pos_edge   (scl_pos_edge)              ,
              .o_sdr_rx_nack_ack       (ser_nack_ack)              ,
              .o_sdr_rx_rd_abort       (sdr_rx_rd_abort)           , //to fsm 
              .o_sdr_rx_regf_data_wr   (regf_data_wr)              ,
              .o_sdr_rx_mode_done      (rx_mode_done)              ,
              .o_sdr_rx_pp_mode_done   (rx_pp_mode_done)           ,
              .o_crh_start_detected    (start_detected)            , 
              .last_bit_flag           (last_bit)                  );


frame_counter u_frame_counter (
             .i_fcnt_no_frms         (fcnt_no_frms)        , 
             .i_fcnt_clk             (i_sdr_clk)           , 
             .i_fcnt_rst_n           (i_sdr_rst_n)         ,
             .i_fcnt_en              (sdr_ctrl_fcnt_en)    , 
             .o_fcnt_last_frame      (sdr_ctrl_last_frame));


/*sdr_mode        u_sdr_mode(
               .i_sdr_ctrl_clk               (i_sdr_clk)                    ,       
               .i_sdr_ctrl_rst_n             (i_sdr_rst_n)                  ,
               .i_sdr_ctrl_cnt_done          (sdr_ctrl_cnt_done)            ,
               .i_i3c_ctrl_sdr_en            (i_i3c_ctrl_sdr_en)            ,
               .i_sdr_ctrl_last_frame        (sdr_ctrl_last_frame)          ,
               .i_ser_mode_done              (ser_mode_done)                ,
               .i_deser_mode_done            (rx_mode_done)                 ,
               .i_sdr_regf_rx_tx                (ser_rx_tx)                 ,
               .i_ser_nack_ack               (ser_nack_ack)                 ,
               .i_ser_to_par_trans         (ser_to_parity_transition)       ,
               .i_sdr_ctrl_bit_cnt_done      (sdr_ctrl_cnt_done)            ,
               .i_sdr_rx_rd_abort            (sdr_rx_rd_abort)              ,
               .i_sdr_ctrl_scl_neg_edge       (scl_neg_edge)                , 
               .i_sdr_ctrl_scl_stall_done          (scl_stall_done)         ,
               .i_sdr_ctrl_scl_pos_edge          (scl_pos_edge)             ,
               .o_sdr_ctrl_scl_stall_cycles         (scl_stall_cycles)      ,
               .o_sdr_ctrl_scl_stall_flag            (stall_flag)           ,
               .o_sdr_ctrl_fcnt_en           (sdr_ctrl_fcnt_en)             ,
               .o_sdr_ctrl_ser_en            (sdr_ctrl_ser_en)              ,
               .o_sdr_ctrl_ser_valid         (sdr_ctrl_ser_valid)           ,
               .o_sdr_ctrl_ser_mode          (sdr_ctrl_ser_mode)            ,
               .o_sdr_ctrl_deser_en          (sdr_ctrl_deser_en)            ,
               .o_sdr_rx_mode                (sdr_rx_mode)                  ,
               .o_sdr_ctrl_cnt_en            (sdr_cnt_en)                   ,
               .o_sdr_ctrl_rx_cnt_en         (sdr_ctrl_rx_cnt_en)           ,
               .o_sdr_ctrl_pp_od             (sdr_ctrl_pp_od)               ,
               .o_sdr_ctrl_addr_done         (sdr_ctrl_addr_done)           ,
               .o_sdr_ctrl_done              (o_sdr_ctrl_done)              ,
               .o_sdr_ctrl_regf_wr_en        (regf_wr_en)                   ,
               .o_sdr_ctrl_regf_rd_en_pulse  (regf_rd_en)                   ,
               .o_sdr_ctrl_regf_addr         (regf_addr)                    ,              
               .o_sdr_ctrl_rx_valid          (sdr_rx_valid)                 ,
               .o_sdr_ctrl_scl_idle          (sdr_ctrl_scl_idle)           ); */
  

controller_TX u_controller_tx (                                             
              .i_clk                     (i_sdr_clk)                 , 
              .i_rst_n                   (i_sdr_rst_n)               ,
              .i_ser_scl                 (scl)                       ,
              .i_ser_scl_pos_edge        (scl_pos_edge)              ,
              .i_ser_scl_neg_edge        (scl_neg_edge)              ,
              .i_ser_pp_od               (sdr_ctrl_pp_od)               ,
              .i_ser_en                  (sdr_ctrl_ser_en)           ,
              .i_ser_valid               (sdr_ctrl_ser_valid)        , 
              .i_ser_count               (sdr_cnt_bit_count)         ,
              .i_ser_count_done          (sdr_ctrl_cnt_done)         , 
              .i_ser_mode                (sdr_ctrl_ser_mode)         ,
              .i_ser_regf_data           (regf_data_rd)              , 
              .i_timer_cas               (i_crh_timer_cas)           ,
              .o_stop_pattern            (stop_pattern)             ,
              .o_start_pattern           (start_pattern)            ,     
              .o_ser_s_data              (ser_s_data)                ,
              .o_ser_mode_done           (ser_mode_done)             ,
              .o_ser_pp_mode_done        (ser_pp_mode_done)          ,
              .o_tx_daa_done             (tx_daa_done)                ,
              .o_ser_to_parity_transition (ser_to_parity_transition) ,
              .o_ser_sda_low              (sda_low) ); 
              // will be handeled after scl handeling


sda_handling u_sda_handling (
            .i_handling_s_data       (ser_s_data)          ,
            .i_handling_sel_pp_od    (sdr_ctrl_pp_od)      ,             
            .i_handling_pp_en        (sdr_ctrl_ser_en)      , // same enable of the serializer
            .o_handling_s_data       (deser_s_data)        ,
            .sda                     (sda)                );

scl_generation u_scl_generation (  
              .i_sdr_ctrl_clk          (i_sdr_clk)           ,
              .i_sdr_ctrl_rst_n        (i_sdr_rst_n)         ,
              .i_sdr_scl_gen_pp_od     (sdr_ctrl_pp_od)      ,
              .i_scl_gen_stall         (scl_gen_stall)       , 
              .i_sdr_ctrl_scl_idle     (sdr_ctrl_scl_idle)   ,
              .o_scl_pos_edge          (scl_pos_edge)        ,
              .o_scl_neg_edge          (scl_neg_edge)        ,
              .o_scl                   (scl)                );
              
              
reg_file u_reg_file (
              .i_regf_clk            (i_sdr_clk)         ,     
              .i_regf_rst_n          (i_sdr_rst_n)       ,     
              .i_regf_rd_en          (regf_rd_en)        ,     
              .i_regf_wr_en          (regf_wr_en)      ,
              .i_regf_addr           (regf_addr)         , 
              .i_regf_data_wr        (regf_data_wr)      , 
              .o_regf_data_rd        (regf_data_rd)      ,
              .o_ser_rx_tx           (ser_rx_tx)         ,
              .o_regf_num_frames     (fcnt_no_frms)      ,
              .o_crh_CRHDLY          (CRHDLY)            ,
	            .o_crh_getstatus_data  (getstatus_data)    ,
	            .o_crh_CRCAP2          (CRCAP2)            ,
	            .o_crh_PRECR           (PRECR)             ,
	            .o_crh_cfg_reg         (cfg_reg)           ,
	            .o_crh_tgts_count      (tgts_count)        );             
              
scl_staller u_scl_staller(
                .i_stall_clk(i_sdr_clk),
                .i_stall_rst_n(i_sdr_rst_n),
                .i_stall_flag(stall_flag),
                .i_stall_cycles(scl_stall_cycles),
                .o_stall_done(scl_stall_done),
                .o_scl_stall (scl_gen_stall)
    );
                  



endmodule
`default_nettype wire


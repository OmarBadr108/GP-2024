//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors: Yaseen Salah
// Revision: 
//
// Version : 1.0
//
// Create Date:  21:34:01 25/03/2023 
// Design Name:  top_for_hj_test
// Module Name:  top_for_hj_test 
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


`default_nettype none

module top_for_hj_test (
    input  wire       i_sdr_clk                 , // system clk
    input  wire       i_sdr_rst_n               , // asynch neg edge reset 
    //input  wire       i_i3c_ctrl_sdr_en         , // sdr block enable signal 
    inout  wire       sda                       , // sda bus
    output wire       scl                	    , // scl bus      
    output wire       o_sdr_rx_valid            , // output to host >> valid data are loaded
    output wire       o_sdr_ctrl_done           ,

////////////////////////////VIRTUAL INPUTS FOR SIMULATION////////////////////////////
    input  wire       i_hot_join_enable         , //Hot-Join Enable-Signal
    input  wire       i_hot_join_ccc            , //Sending Hot-Join CCCs Request (if Host wanna ENHJ or DISHJ without prior HJ Request)
    input  wire       i_hot_join_support        , //CRCAP1[0] Hardcoded (read-only) [1 >> Supported , 0 >> Not Supported]
    input  wire [2:0] i_hot_join_configuration  , //HJ Configuration register {AVAL/BUSY , EN/DIS , ACK/NACK} (Host can overwrite at any time)
////////////////////////////VIRTUAL OUTPUTS FOR SIMULATION////////////////////////////
    output wire       o_hot_join_daa_req        , //DAA Procedure Request (Suggestion: Trigger DAA directly for time optimization)
    output wire       o_hot_join_ctrl_role_pass , //CRR Procedure Request (Suggestion: Trigger CRH directly for time optimization)
    output wire       o_hot_join_acc_rej        , //Hot-Join Request Accepted/Rejected flag [1 >> ACCEPTED , 0 >> REJECTED]
    output wire       o_hot_join_done             //Hot-Join Block Done-Flag 

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
    wire      [5:0]      regf_addr                 ;
    wire      [7:0]      regf_data_wr              ;
    wire      [7:0]      regf_data_rd              ;
    wire                 ser_rx_tx                 ;
    wire                 sdr_rx_valid              ;    
    wire      [7:0]      enec_byte                 ;
    wire      [7:0]      disec_byte                ;

    wire i_i3c_ctrl_sdr_en 						   ;

assign i_i3c_ctrl_sdr_en = (i_hot_join_enable)? 0 : 1 ;
assign o_sdr_rx_valid = sdr_rx_valid ; 

hot_join u_hot_join ( 
			.i_hot_join_clk              (i_sdr_clk)                 ,
			.i_hot_join_rst_n            (i_sdr_rst_n)               ,
			.i_hot_join_enable           (i_hot_join_enable)         ,
			.i_hot_join_ccc              (i_hot_join_ccc)            ,
			.i_hot_join_support          (i_hot_join_support)        ,
			.i_hot_join_configuration    (i_hot_join_configuration)  ,
			.i_hot_join_tx_mode_done     (ser_mode_done)             ,
			.i_hot_join_rx_mode_done     (rx_mode_done)              ,
			.i_hot_join_nack_ack         (ser_nack_ack)              ,
            .i_hot_join_scl_neg_edge     (scl_neg_edge)              ,
            .i_hot_join_scl_pos_edge     (scl_pos_edge)              ,

            //.i_hot_join_scl_stall_done   (scl_stall_done)            ,
            //.o_hot_join_scl_stall_cycles (scl_stall_cycles)          ,
            //.o_hot_join_scl_stall_flag   (stall_flag)                ,

			.o_hot_join_tx_en            (sdr_ctrl_ser_en)           ,
			.o_hot_join_tx_mode          (sdr_ctrl_ser_mode)         ,
			.o_hot_join_rx_en            (sdr_ctrl_deser_en)         ,
			.o_hot_join_rx_mode          (sdr_rx_mode)               ,
			.o_hot_join_regf_rd_en       (regf_rd_en)                ,
            .o_hot_join_regf_wr_en       (sdr_rx_valid)              ,
			.o_hot_join_regf_addr        (regf_addr)                 ,
			.o_hot_join_def_byte_enhj    (enec_byte[3])              ,
			.o_hot_join_def_byte_dishj   (disec_byte[3])             ,
			.o_hot_join_cnt_en           (sdr_cnt_en)                ,
			.o_hot_join_pp_od            (sdr_ctrl_pp_od)            ,
			.o_hot_join_daa_req          (o_hot_join_daa_req)        ,
			.o_hot_join_ctrl_role_pass   (o_hot_join_ctrl_role_pass) ,
			.o_hot_join_acc_rej          (o_hot_join_acc_rej)        ,
			.o_hot_join_done             (o_hot_join_done)          );

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
              .i_sdr_rx_mode           (sdr_rx_mode)               ,
              .i_fcnt_last_frame       (sdr_ctrl_last_frame)       ,
              .o_sdr_rx_nack_ack       (ser_nack_ack)              ,
              .o_sdr_rx_rd_abort       (sdr_rx_rd_abort)           , //to fsm 
              .o_sdr_rx_regf_data_wr   (regf_data_wr)              ,
              .o_sdr_rx_mode_done      (rx_mode_done)             );


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
               .o_sdr_ctrl_scl_idle          (sdr_ctrl_scl_idle)           );*/
  

controller_tx u_controller_tx (                                             
            .i_clk                     (i_sdr_clk)                 , 
            .i_rst_n                   (i_sdr_rst_n)               ,
            .i_ser_scl                 (scl)                       ,
            .i_ser_en                  (sdr_ctrl_ser_en)           ,
            .i_ser_valid               (sdr_ctrl_ser_valid)        , 
            .i_ser_count               (sdr_cnt_bit_count)         ,
            .i_ser_count_done          (sdr_ctrl_cnt_done)         , 
            .i_ser_mode                (sdr_ctrl_ser_mode)         ,
            .i_ser_regf_data           (regf_data_rd)              ,   
            .i_ser_scl_neg_edge        (scl_neg_edge)              ,
            .i_ser_scl_pos_edge        (scl_pos_edge)              ,
            //.i_ser_pp_od               (sdr_ctrl_pp_od)            ,
            .o_ser_s_data              (ser_s_data)                ,
            .o_ser_mode_done           (ser_mode_done)             ,
            .o_ser_to_parity_transition (ser_to_parity_transition)); 
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
              .i_regf_wr_en          (sdr_rx_valid)      ,
              .i_regf_addr           (regf_addr)         , 
              .i_regf_data_wr        (regf_data_wr)      , 
              .i_enec_byte           (enec_byte)         ,
              .i_disec_byte          (disec_byte)        ,
              .o_regf_data_rd        (regf_data_rd)      ,
              .o_ser_rx_tx           (ser_rx_tx)         ,
              .o_regf_num_frames     (fcnt_no_frms)     );             
              
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

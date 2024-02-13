`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors: Mostafa Hassan
// 
// Revision:   
//
// Version : 1.0
//
// Create Date:  12:00 10/04/2023
// Design Name:  controller_crh_tb
// Module Name:  controller_crh_tb 
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


module controller_crh_tb ();
  //input wires testbench
  reg          i_sdr_clk_tb              ;
  reg          i_sdr_rst_n_tb            ;
  wire         sda_tb                    ;
  reg          i_crh_en_tb               ;
  reg   [7:0]  i_crh_CRHDLY_tb           ;
  reg   [7:0]  i_crh_getstatus_data_tb   ;
  reg   [7:0]  i_crh_CRCAP2_tb           ;
  reg   [7:0]  i_crh_PRECR_tb            ;
  reg   [7:0]  i_crh_cfg_reg_tb          ;
  reg   [7:0]  i_crh_tgts_count_tb       ;
  reg          i_crh_crhpoverlap_tb      ;
  reg          i_crh_newcrlock_tb        ;
  reg          i_crh_timer_cas_tb        ;
  //output wires testbench
  wire         scl_tb                    ;  
  wire         o_sdr_rx_valid_tb         ;
  wire         o_sdr_ctrl_done_tb        ;
  wire         o_crh_done_tb             ;
  wire         o_crh_ncr_win_tb          ;
  wire         o_crh_ncr_take_control_tb ;


  reg          sda_drive                 ;
  wire         sda_recv                  ;
  
assign sda_tb = sda_drive ;
assign sda_recv = sda_tb  ;
//DUT instantiation 
top_for_crh_test DUT (
                    .i_sdr_clk              (i_sdr_clk_tb)              ,
                    .i_sdr_rst_n            (i_sdr_rst_n_tb)            ,
                    .sda                    (sda_tb)                    ,
                    .scl                    (scl_tb)                    ,
                    .o_sdr_rx_valid         (o_sdr_rx_valid_tb)         ,
                    .o_sdr_ctrl_done        (o_sdr_ctrl_done_tb)        ,
                    .i_crh_en               (i_crh_en_tb)               ,
                    .i_crh_CRHDLY           (i_crh_CRHDLY_tb)           ,
                    .i_crh_getstatus_data   (i_crh_getstatus_data_tb)   ,
                    .i_crh_CRCAP2           (i_crh_CRCAP2_tb)           ,
                    .i_crh_PRECR            (i_crh_PRECR_tb)            ,
                    .i_crh_cfg_reg          (i_crh_cfg_reg_tb)          ,
                    .i_crh_tgts_count       (i_crh_tgts_count_tb)       ,
                    .i_crh_crhpoverlap      (i_crh_crhpoverlap_tb)      ,
                    .i_crh_newcrlock        (i_crh_newcrlock_tb)        ,
                    .i_crh_timer_cas        (i_crh_timer_cas_tb)        ,
                    .o_crh_done             (o_crh_done_tb)             ,
                    .o_crh_ncr_win          (o_crh_ncr_win_tb)          ,
                    .o_crh_ncr_take_control (o_crh_ncr_take_control_tb) );



//clock generation
always #10 i_sdr_clk_tb = ~i_sdr_clk_tb  ; //20ns clk period

//initial block
initial 
  begin
    sda_drive = 1'bz ;
    i_sdr_clk_tb = 1'b0 ;
    //reseting all signals
    i_sdr_rst_n_tb = 1'b1 ;
    #20
    i_sdr_rst_n_tb = 1'b0 ;
    #20 
    i_sdr_rst_n_tb = 1'b1 ;
    //case1
    i_crh_en_tb = 1'b1 ;
    i_crh_cfg_reg_tb = 8'h03 ; //controller role request and the active controller will ack 
    @(posedge o_crh_done_tb) i_crh_en_tb = 1'b0 ;
    
    #98000
    $stop ;
  end
    
    
    
      
    
    
    
    

  

endmodule  
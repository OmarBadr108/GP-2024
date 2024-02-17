//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Yaseen Salah , Nour Eldeen Samir , Yousseff Amr ,  Youssef Essam Noaman , Zyad Sobhy , Mostafa Hassan
// Revision: 
// Version : 1.0
// 
// Create Date:  7:46 PM     29/3/2023 
// Design Name:  I3C Engine
// Module Name:  i3c_engine
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
////////////////////////////////////////////////////////////////////////////////////

`default_nettype none

module i3c_engine (
    input   wire          i_clk                     ,
    input   wire          i_rst_n                   ,
    input   wire          i_controller_en           , //from device configuration of Controller/Target role
    input   wire          i_i3c_i2c_sel             ,
    input   wire          i_sdr_done                ,
    input   wire          i_i2c_done                ,
    input   wire          i_daa_done                ,
    input   wire          i_daa_error               ,
    input   wire          i_hj_done                 , //Hot-Join Block Done-Flag 
    input   wire          i_hj_acc_rej              , //Hot-Join Request Accepted/Rejected flag [1 >> ACCEPTED , 0 >> REJECTED]
    input   wire          i_hj_daa_req              , //DAA Procedure Request (Suggestion: Trigger DAA directly for time optimization)
    input   wire          i_hj_cr_pass              , //CRR Procedure Request (Suggestion: Trigger CRH directly for time optimization)
    input   wire          i_tx_mode_done            , //Tx Current Mode Done-Flag 
    input   wire          i_rx_mode_done            , 
    input   wire          i_target_nack             , //Error-Flag (Target doesn't ACK)
    input   wire          i_rx_arbitration_lost     ,
    input   wire          i_scl_pos_edge            ,
    input   wire          i_scl_neg_edge            ,
    input   wire  [7:0]   i_regf_data_rd            ,
    input   wire          i_timer_cas               , // input from timer block >> t clock after start is done 
    input   wire          i_ccc_en_dis_hj           , //from an external input, for enable/disable events to prevent Bus-Initialization or DAA interruptions.
    input   wire          i_ibi_payload_en          ,
    input   wire          i_sdr_ibi_payload_done    ,
    input   wire          i_ibi_done                ,
    input   wire          i_crh_done              ,    
    //input   wire          i_crh_ncr_win           ,
    //input   wire          i_crh_ncr_take_control  ,
    input   wire          i_crh_send_stop           ,


    ///////////////////////hdr//////////////////////////////////
    input   wire          i_hdr_en                    ,
    input   wire          i_enthdr_done               ,
    input   wire          i_hdrengine_exit          ,
    ////////////////////////////////////////////////////////////
    output  reg           o_sdr_en                  ,
    output  reg           o_i2c_en                  , 
    output  reg           o_daa_en                  ,
    output  reg           o_ibi_en                  ,
    output  reg           o_hj_en                   , //Hot-Join Enable-Signal
    output  reg           o_hj_ccc                  , //Sending Hot-Join CCCs Request (if Host wanna ENHJ or DISHJ without prior HJ Request)
    output  reg           o_hj_daa_en               , //enables DAA directly after HJ with an internal Repeated_Start
    output  reg           o_hj_crh_en               , //enables CRH directly after HJ with an internal Repeated_Start
    output  reg           o_crh_en                  ,
    output  reg           o_crh_stop_is_sent        ,
    output  reg           o_tx_en                   , //Tx Enable-Flag
    output  reg   [2:0]   o_tx_mode                 , //Tx Current Mode Selector 
    output  reg           o_rx_data_valid           ,
    output  reg           o_pp_od                   , //Push-Pull/Open-Drain Selector (Always = 0 in I2C)
    output  reg           o_scl_idle                , // helds the scl to idle
    output  reg           o_bit_cnt_en              ,
    output  reg           o_regf_rd_en              ,
    output  reg   [2:0]   o_regf_rd_en_mux_sel      ,
    output  reg   [2:0]   o_regf_rd_address_mux_sel ,
    output  reg   [2:0]   o_regf_wr_en_mux_sel      ,
    output  reg   [2:0]   o_scl_pp_od_mux_sel       ,
    output  reg   [2:0]   o_tx_en_mux_sel           ,
    output  reg   [2:0]   o_tx_mode_mux_sel         ,
    output  reg   [2:0]   o_rx_en_mux_sel           ,
    output  reg   [2:0]   o_rx_mode_mux_sel         ,
    output  reg   [2:0]   o_bit_cnt_en_mux_sel      ,
    output  reg   [2:0]   o_bit_rx_cnt_en_mux_sel   ,
    output  reg   [2:0]   o_fcnt_en_mux_sel         ,
    output  reg   [2:0]   o_scl_idle_mux_sel        ,
    output  reg   [2:0]   o_fcnt_no_frms_sel        ,
    output  reg   [2:0]   o_ser_rx_tx_mux_sel       ,
    output  reg           o_i3c_idle_flag           ,
    output  reg   [2:0]   o_scl_stall_flag_sel      ,
    output  reg   [2:0]   o_scl_stall_cycles_sel    ,
    output  reg           o_controller_done         ,
    output  reg   [2:0]   o_bits_cnt_regf_rx_tx_sel ,
    
    ///////////////////////hdr//////////////////////////////////
    output  reg          o_enthdr_en                 
   
);


//-------------------------------- states encoding in gray --------------------------------------------
localparam IDLE              = 4'b0000 ; 
localparam START             = 4'b0001 ;
localparam SDR_MODE          = 4'b0010 ;
localparam IBI               = 4'b0011 ;
localparam I2C_MODE          = 4'b0110 ;
localparam STOP              = 4'b1111 ;
localparam ARBITRATION       = 4'b1100 ;
localparam HOT_JOIN          = 4'b1110 ;
localparam CTRL_REQ          = 4'b1010 ;
localparam DAA               = 4'b0100 ;
localparam ENTHDR            = 4'b1101 ;


//--------------------------------- Mux Selection Parameters -----------------------------------------
localparam SDR_SEL        = 3'b000 ;
localparam I2C_SEL        = 3'b001 ;
localparam I3C_ENGINE_SEL = 3'b010 ;
localparam DAA_SEL        = 3'b011 ;
localparam HJ_SEL         = 3'b100 ;
localparam IBI_SEL        = 3'b101 ;
localparam CRH_SEL        = 3'b110 ;
localparam ENTHDR_SEL     = 3'b111 ;


//--------------------------------- Mode (HDR OR SDR) -----------------------------------------
localparam SDR_MODE_SEL     = 1'b0 ;
localparam HDR_MODE_SEL     = 1'b1 ;



//--------------------------------- internal wires declaration ------------------------------------------
reg [3:0] state ;
reg write_adress_to_regf    ;
reg arbitrated_adress_ready ;
reg dynamic_address_assigned ;
reg send_stop ;
//--------------------------------- controller main fsm -------------------------------------------------

always @(posedge i_clk or negedge i_rst_n) 
  begin: controller_main_fsm
    
    if (!i_rst_n) 
        begin
            o_sdr_en          <= 1'b0   ;  
            o_i2c_en          <= 1'b0   ;
            o_daa_en          <= 1'b0   ; 
            o_hj_en           <= 1'b0   ;
            o_crh_en          <= 1'b0   ;
            o_hj_ccc          <= 1'b0   ;
            o_ibi_en          <= 1'b0 ;
            o_crh_en          <= 1'b0 ;
            o_tx_en           <= 1'b0   ; 
            o_tx_mode         <= 3'b000 ; 
            o_pp_od           <= 1'b0   ;   
            o_controller_done <= 1'b0   ; 
            o_rx_data_valid   <= 1'b0   ;
            o_bit_cnt_en      <= 1'b0   ;
            o_regf_rd_en      <= 1'b0   ;
            o_i3c_idle_flag   <= 1'b0   ; 
            o_crh_stop_is_sent <= 1'b0 ;

            /////////////       internal wires      ///////////////////

            arbitrated_adress_ready <=  1'b0 ;
            write_adress_to_regf    <=  1'b0 ;
            dynamic_address_assigned <= 1'b1 ; //for TESTINGGGGG


            state             <= IDLE   ;          
        end

    else
        begin
            case(state)
            IDLE:
                begin
                    o_sdr_en             <= 1'b0           ;
                    o_i3c_idle_flag      <= 1'b0           ;  
                    o_i2c_en             <= 1'b0           ; 
                    o_hj_en              <= 1'b0           ;
                    o_hj_ccc             <= 1'b0           ;
                    o_crh_en             <= 1'b0           ;
                    o_tx_en              <= 1'b0           ; 
                    o_tx_mode            <= 3'b000         ;
                    o_pp_od              <= 1'b0           ; 
                    o_controller_done    <= 1'b0           ; 
                    o_scl_idle           <= 1'b1           ; 
                    o_rx_data_valid      <= 1'b0           ;
                    o_scl_idle_mux_sel   <= I3C_ENGINE_SEL ;
                    o_bit_cnt_en_mux_sel <= I3C_ENGINE_SEL ; 
                    o_fcnt_no_frms_sel   <= I3C_ENGINE_SEL ; 
                    o_ser_rx_tx_mux_sel  <= I3C_ENGINE_SEL                 ;
                    o_crh_stop_is_sent <= 1'b0 ;

                    if (i_controller_en)
                        begin
                            o_tx_en             <= 1'b1           ; 
                            o_tx_mode           <= 3'b000         ; //START MODE
                            o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                            o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                            o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                            state               <= START          ;
                        end
                    else if (i_rx_arbitration_lost)
                        begin
                            o_regf_wr_en_mux_sel <= I3C_ENGINE_SEL ;
                            state                <= ARBITRATION    ; 
                        end 
                    else
                        begin
                            state <= IDLE ;
                        end
                end

            /////////////////---START STATE---//////////////////
            START:
                begin 
                    o_scl_idle <= 1'b0 ;
                    if (i_tx_mode_done)
                        begin
                            o_tx_en   <= 1'b1   ; 
                            o_tx_mode <= 3'b000 ; 
                            o_pp_od   <= 1'b0   ;
                            if (i_ccc_en_dis_hj) //for enable/disable events to prevent Bus-Initialization or DAA interruptions.
                                begin
                                    o_hj_en                   <= 1'b1     ;
                                    o_hj_ccc                  <= 1'b1     ;
                                    o_regf_rd_address_mux_sel <= HJ_SEL   ;
                                    o_regf_wr_en_mux_sel      <= HJ_SEL   ;
                                    o_scl_pp_od_mux_sel       <= HJ_SEL   ;
                                    o_tx_en_mux_sel           <= HJ_SEL   ;
                                    o_tx_mode_mux_sel         <= HJ_SEL   ;
                                    o_rx_en_mux_sel           <= HJ_SEL   ;
                                    o_rx_mode_mux_sel         <= HJ_SEL   ;
                                    o_bit_cnt_en_mux_sel      <= HJ_SEL   ;
                                    o_bit_rx_cnt_en_mux_sel   <= HJ_SEL   ;
                                    o_fcnt_en_mux_sel         <= HJ_SEL   ;
                                    o_fcnt_no_frms_sel        <= HJ_SEL   ;
                                    o_regf_rd_en_mux_sel      <= HJ_SEL   ; 
                                    state                     <= HOT_JOIN ;
                                end
                            else if (!dynamic_address_assigned && i_i3c_i2c_sel)
                                begin
                                    o_daa_en                  <= 1'b1    ;                 
                                    o_regf_rd_address_mux_sel <= DAA_SEL ;
                                    o_regf_wr_en_mux_sel      <= DAA_SEL ;
                                    o_scl_pp_od_mux_sel       <= DAA_SEL ;
                                    o_tx_en_mux_sel           <= DAA_SEL ;
                                    o_tx_mode_mux_sel         <= DAA_SEL ;
                                    o_rx_en_mux_sel           <= DAA_SEL ;
                                    o_rx_mode_mux_sel         <= DAA_SEL ;
                                    o_bit_cnt_en_mux_sel      <= DAA_SEL ;
                                    o_bit_rx_cnt_en_mux_sel   <= DAA_SEL ;
                                    o_fcnt_en_mux_sel         <= DAA_SEL ;
                                    o_fcnt_no_frms_sel        <= DAA_SEL ;
                                    o_regf_rd_en_mux_sel      <= DAA_SEL ; 
                                    state                     <= DAA     ;
                                end
                            else
                                begin 
                                    case (i_i3c_i2c_sel)
                                    1'b1: 
                                    //////////////////////////////ENTHDR///////////////////////////////
                                        begin
                                           if(i_hdr_en) //input from outside (configration) >> ENABLES THE ENTHDR BLOCK
                                            begin
                                             o_enthdr_en               <= 1'b1       ; //enables enthdr block
                                             o_regf_rd_en_mux_sel      <= ENTHDR_SEL ;
                                             o_regf_rd_address_mux_sel <= ENTHDR_SEL ;
                                             o_regf_wr_en_mux_sel      <= ENTHDR_SEL ;
                                             o_scl_pp_od_mux_sel       <= ENTHDR_SEL ;
                                             o_tx_en_mux_sel           <= ENTHDR_SEL ;
                                             o_tx_mode_mux_sel         <= ENTHDR_SEL ;
                                             o_rx_en_mux_sel           <= ENTHDR_SEL ;
                                             o_rx_mode_mux_sel         <= ENTHDR_SEL ;
                                             o_bit_cnt_en_mux_sel      <= ENTHDR_SEL ;
                                             o_bit_rx_cnt_en_mux_sel   <= ENTHDR_SEL ;
                                             o_fcnt_en_mux_sel         <= ENTHDR_SEL ;
                                             o_scl_idle_mux_sel        <= ENTHDR_SEL ; 
                                             state                     <= ENTHDR;
                                            end
                                  /////////////////////////////////////////////////////////////////////
                                           else 
                                            begin
                                             o_sdr_en                  <= 1'b1     ;
                                             o_sda_sel                 <= SDR_MODE_SEL    ; 
                                             o_regf_rd_en_mux_sel      <= SDR_SEL  ;
                                             o_regf_rd_address_mux_sel <= SDR_SEL  ;
                                             o_regf_wr_en_mux_sel      <= SDR_SEL  ;
                                             o_scl_pp_od_mux_sel       <= SDR_SEL  ;
                                             o_tx_en_mux_sel           <= SDR_SEL  ;
                                             o_tx_mode_mux_sel         <= SDR_SEL  ;
                                             o_rx_en_mux_sel           <= SDR_SEL  ;
                                             o_rx_mode_mux_sel         <= SDR_SEL  ;
                                             o_bit_cnt_en_mux_sel      <= SDR_SEL  ;
                                             o_bit_rx_cnt_en_mux_sel   <= SDR_SEL  ;
                                             o_fcnt_en_mux_sel         <= SDR_SEL  ;
                                             o_scl_idle_mux_sel        <= SDR_SEL  ; 
                                             state                     <= SDR_MODE ;
                                            end

                                      end 
                                    1'b0: 
                                        begin
                                            o_i2c_en <= 1'b1     ;
                                            state    <= I2C_MODE ;
                                        end 
                                    endcase
                                end
                        end
                    else 
                        begin
                            state <= START ;
                        end
                end
            
            ARBITRATION: 
                begin 
                    if (i_rx_mode_done && i_scl_neg_edge) 
                        begin
                            o_rx_data_valid      <= 1'b1 ;
                            o_bit_cnt_en         <= 1'b0 ;
                            write_adress_to_regf <= 1'b1 ;
                        end
                    else if (arbitrated_adress_ready && i_scl_neg_edge)
                        begin 
                         if (i_regf_data_rd == {7'h02,1'b0})  /// hotjoin address
                             begin 
                                o_hj_en                   <= 1'b1     ;
                                o_hj_ccc                  <= 1'b0     ;
                                o_regf_rd_en_mux_sel      <= HJ_SEL   ;
                                o_regf_rd_address_mux_sel <= HJ_SEL   ;
                                o_regf_wr_en_mux_sel      <= HJ_SEL   ;
                                o_scl_pp_od_mux_sel       <= HJ_SEL   ;
                                o_tx_en_mux_sel           <= HJ_SEL   ;
                                o_tx_mode_mux_sel         <= HJ_SEL   ;
                                o_rx_en_mux_sel           <= HJ_SEL   ;
                                o_rx_mode_mux_sel         <= HJ_SEL   ;
                                o_bit_cnt_en_mux_sel      <= HJ_SEL   ;
                                o_bit_rx_cnt_en_mux_sel   <= HJ_SEL   ;
                                o_fcnt_en_mux_sel         <= HJ_SEL   ;
                                o_scl_idle_mux_sel        <= HJ_SEL   ;
                                o_fcnt_no_frms_sel        <= HJ_SEL   ;
                                state                     <= HOT_JOIN ;
                             end
                            else if (i_regf_data_rd[0]==1'b1)  /// IBI requesr
                              begin 
                                state <= IBI ;
                              end 
                            else if (i_regf_data_rd[0]==1'b0) /// Controller role request
                              begin
                                o_crh_en <= 1'b1 ; //controle role handoff enable signal
                                o_hj_crh_en <= 1'b0     ; //controle role request
                                state <= CTRL_REQ ;
                                o_regf_rd_en_mux_sel      <= CRH_SEL   ;
                                o_regf_rd_address_mux_sel <= CRH_SEL   ;
                                o_regf_wr_en_mux_sel      <= CRH_SEL   ;
                                o_scl_pp_od_mux_sel       <= CRH_SEL   ;
                                o_tx_en_mux_sel           <= CRH_SEL   ;
                                o_tx_mode_mux_sel         <= CRH_SEL   ;
                                o_rx_en_mux_sel           <= CRH_SEL   ;
                                o_rx_mode_mux_sel         <= CRH_SEL   ;
                                o_bit_cnt_en_mux_sel      <= CRH_SEL   ;
                                o_bit_rx_cnt_en_mux_sel   <= CRH_SEL   ;
                                o_fcnt_en_mux_sel         <= CRH_SEL   ;
                                o_scl_idle_mux_sel        <= CRH_SEL   ;
                                o_fcnt_no_frms_sel        <= CRH_SEL   ;

                              end 
                        end
                    else if (write_adress_to_regf && o_regf_rd_en )
                        begin
                            arbitrated_adress_ready <= 1'b1 ;
                        end
                    else if (write_adress_to_regf)
                        begin 
                            o_rx_data_valid <= 1'b0 ;
                            o_regf_rd_en    <= 1'b1 ;
                        end
                end
            
            //////////////---MODES AND FEATURES---//////////////
            SDR_MODE:
                begin 
                    o_bit_cnt_en <= 1'b1 ;
                    if (i_sdr_done)
                        begin
                            o_sdr_en            <= 1'b0           ;
                            o_tx_en             <= 1'b1           ; 
                            o_tx_mode           <= 3'b010         ;
                            o_pp_od             <= 1'b1           ; //I3C STOP is driven by Push-Pull
                            o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                            o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                            o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                            o_scl_idle_mux_sel  <= I3C_ENGINE_SEL ;
                            o_bits_cnt_regf_rx_tx_sel <= I3C_ENGINE_SEL  ;  
                            o_ser_rx_tx_mux_sel <= I3C_ENGINE_SEL ; 
                            state               <= STOP           ;
                            //may check i_target_nack and refer an indicator to host
                        end
                    else if (i_rx_arbitration_lost)
                        begin
                            o_sdr_en              <= 1'b0           ;
                            o_tx_en               <= 1'b0           ; 
                            o_tx_en_mux_sel       <= I3C_ENGINE_SEL ;
                            o_regf_wr_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_bit_cnt_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_regf_rd_en_mux_sel  <= I3C_ENGINE_SEL  ;
                            o_ser_rx_tx_mux_sel   <= I3C_ENGINE_SEL  ;
                            state <= ARBITRATION ; 
                        end 
                    else if (i_sdr_ibi_payload_done)
                        begin
                            state <= STOP; 
                            o_ibi_en <= 1'b0 ;
                        end 
                            
                    else
                        begin
                            state <= SDR_MODE ;
                        end
                end
            
            I2C_MODE:
                begin
                    o_regf_rd_en_mux_sel      <= I2C_SEL ;
                    o_regf_rd_address_mux_sel <= I2C_SEL ;
                    o_regf_wr_en_mux_sel      <= I2C_SEL ;
                    o_scl_pp_od_mux_sel       <= I2C_SEL ;
                    o_tx_en_mux_sel           <= I2C_SEL ;
                    o_tx_mode_mux_sel         <= I2C_SEL ;
                    o_rx_en_mux_sel           <= I2C_SEL ;
                    o_rx_mode_mux_sel         <= I2C_SEL ;
                    o_bit_cnt_en_mux_sel      <= I2C_SEL ;
                    o_bit_rx_cnt_en_mux_sel   <= I2C_SEL ;
                    o_fcnt_en_mux_sel         <= I2C_SEL ;
                    o_bits_cnt_regf_rx_tx_sel <= I2C_SEL  ;

                    o_bit_cnt_en              <= 1'b1    ;
                    if (i_i2c_done)
                        begin
                            o_i2c_en            <= 1'b0           ;
                            o_tx_en             <= 1'b1           ; 
                            o_tx_mode           <= 3'b010         ;
                            o_pp_od             <= 1'b0           ; //I2C is always driven by Open-Drain
                            o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                            o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                            o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                            o_scl_idle_mux_sel  <= I3C_ENGINE_SEL ;  
                            state               <= STOP           ;

                            //may check i_target_nack and refer an indicator to host
                        end
                    else if (i_rx_arbitration_lost)
                        begin
                            o_regf_wr_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_bit_cnt_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_regf_rd_en_mux_sel  <= I3C_ENGINE_SEL ;
                            state                 <= ARBITRATION    ; 
                        end 
                    else
                        begin
                            state <= I2C_MODE ;
                        end
                end

            DAA: 
                begin
                    if (i_rx_arbitration_lost)
                        begin
                            o_daa_en <= 1'b0 ; 
                            o_regf_wr_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_bit_cnt_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_regf_rd_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_fcnt_no_frms_sel    <= I3C_ENGINE_SEL ;
                            state                 <= ARBITRATION    ; 
                        end 
                   else if (i_daa_error)
                    begin
                        state <= IDLE ; /// will be editted after adding errors 
                        o_daa_en <= 1'b0 ;
                    end 
                   else if (i_daa_done) 
                        begin
                            o_daa_en                 <= 1'b0 ;
                            dynamic_address_assigned <= 1'b1 ;
                            state                    <= STOP ;
                        end
                end
            
            HOT_JOIN: 
                begin
                    if (i_hj_done)
                        begin
                            o_hj_en <= 1'b0 ;
                            if (i_hj_daa_req)
                                begin
                                    o_daa_en                  <= 1'b1    ;
                                    o_hj_daa_en               <= 1'b1    ;
                                    o_regf_rd_address_mux_sel <= DAA_SEL ;
                                    o_regf_wr_en_mux_sel      <= DAA_SEL ;
                                    o_scl_pp_od_mux_sel       <= DAA_SEL ;
                                    o_tx_en_mux_sel           <= DAA_SEL ;
                                    o_tx_mode_mux_sel         <= DAA_SEL ;
                                    o_rx_en_mux_sel           <= DAA_SEL ;
                                    o_rx_mode_mux_sel         <= DAA_SEL ;
                                    o_bit_cnt_en_mux_sel      <= DAA_SEL ;
                                    o_bit_rx_cnt_en_mux_sel   <= DAA_SEL ;
                                    o_fcnt_en_mux_sel         <= DAA_SEL ;
                                    o_fcnt_no_frms_sel        <= DAA_SEL ;
                                    o_regf_rd_en_mux_sel      <= DAA_SEL ; 
                                    state                     <= DAA     ;
                                end
                            else if (i_hj_cr_pass)
                                begin
                                    o_crh_en    <= 1'b1     ; //CRH main enable signal = 1
                                    o_hj_crh_en <= 1'b1     ; //initiated by active controller 
                                    ////CRH SELECTORS////
                                    state       <= CTRL_REQ ;
                                     o_regf_rd_en_mux_sel      <= CRH_SEL   ;
                                     o_regf_rd_address_mux_sel <= CRH_SEL   ;
                                     o_regf_wr_en_mux_sel      <= CRH_SEL   ;
                                     o_scl_pp_od_mux_sel       <= CRH_SEL   ;
                                     o_tx_en_mux_sel           <= CRH_SEL   ;
                                     o_tx_mode_mux_sel         <= CRH_SEL   ;
                                     o_rx_en_mux_sel           <= CRH_SEL   ;
                                     o_rx_mode_mux_sel         <= CRH_SEL   ;
                                     o_bit_cnt_en_mux_sel      <= CRH_SEL   ;
                                     o_bit_rx_cnt_en_mux_sel   <= CRH_SEL   ;
                                     o_fcnt_en_mux_sel         <= CRH_SEL   ;
                                     o_scl_idle_mux_sel        <= CRH_SEL   ;
                                     o_fcnt_no_frms_sel        <= CRH_SEL   ;
                                end
                            //no need for hj_acc_rej till now
                            else
                                begin
                                    o_tx_en             <= 1'b1           ; 
                                    o_tx_mode           <= 3'b010         ;
                                    o_pp_od             <= 1'b1           ; //I3C STOP is driven by Push-Pull
                                    o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                                    o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                                    o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                                    o_scl_idle_mux_sel  <= I3C_ENGINE_SEL ;  
                                    state               <= STOP           ;
                                end
                        end
                    /*else if (i_rx_arbitration_lost)
                        begin
                            o_hj_en               <= 1'b0           ;
                            o_regf_wr_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_bit_cnt_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_regf_rd_en_mux_sel  <= I3C_ENGINE_SEL ;
                            o_fcnt_no_frms_sel    <= I3C_ENGINE_SEL ;
                            state                 <= ARBITRATION    ; 
                        end */
                    else
                        begin
                            state <= HOT_JOIN ;
                        end
                end
           
            /////////////////---STOP STATE---////////////////
            STOP:
                begin 
                    o_scl_idle <= 1'b1 ; //Yaseen's Edit 
                    if(i_tx_mode_done && send_stop)
                        begin
                            o_tx_en           <= 1'b0   ; 
                            o_tx_mode         <= 3'b010 ;
                            o_scl_idle <= 1'b0 ;
                            o_regf_rd_en_mux_sel      <= CRH_SEL   ;
                            o_regf_rd_address_mux_sel <= CRH_SEL   ;
                            o_regf_wr_en_mux_sel      <= CRH_SEL   ;
                            o_scl_pp_od_mux_sel       <= CRH_SEL   ;
                            o_tx_en_mux_sel           <= CRH_SEL   ;
                            o_tx_mode_mux_sel         <= CRH_SEL   ;
                            o_rx_en_mux_sel           <= CRH_SEL   ;
                            o_rx_mode_mux_sel         <= CRH_SEL   ;
                            o_bit_cnt_en_mux_sel      <= CRH_SEL   ;
                            o_bit_rx_cnt_en_mux_sel   <= CRH_SEL   ;
                            o_fcnt_en_mux_sel         <= CRH_SEL   ;
                            o_scl_idle_mux_sel        <= CRH_SEL   ;
                            o_fcnt_no_frms_sel        <= CRH_SEL   ;
                            state <= CTRL_REQ ;
                            o_crh_stop_is_sent <= 1'b1 ;
                            send_stop <= 1'b0 ; 
                        end
                    else if (i_tx_mode_done && !send_stop)
                        begin
                            o_tx_en           <= 1'b0   ; 
                            o_tx_mode         <= 3'b010 ;
                            o_pp_od           <= 1'b0   ; 
                            o_controller_done <= 1'b1   ;
                            o_i3c_idle_flag   <= 1'b1   ; 
                            state             <= IDLE   ;
                        end
                    
                end

            IBI: begin
                    o_regf_rd_en_mux_sel      <= IBI_SEL;
                    o_regf_rd_address_mux_sel <= IBI_SEL;
                    o_regf_wr_en_mux_sel      <= IBI_SEL;
                    o_scl_pp_od_mux_sel       <= IBI_SEL;
                    o_tx_en_mux_sel           <= IBI_SEL;
                    o_tx_mode_mux_sel         <= IBI_SEL;
                    o_rx_en_mux_sel           <= IBI_SEL;
                    o_rx_mode_mux_sel         <= IBI_SEL;
                    o_bit_cnt_en_mux_sel      <= IBI_SEL;
                    o_bit_rx_cnt_en_mux_sel   <= IBI_SEL;
                    o_fcnt_en_mux_sel         <= IBI_SEL;
                     o_fcnt_no_frms_sel       <= IBI_SEL;
                     o_ser_rx_tx_mux_sel      <= IBI_SEL;

                    if (i_ibi_payload_en)      
                        begin
                          o_sdr_en                  <= 1'b1     ;
                          o_fcnt_no_frms_sel        <=IBI_SEL  ; // to select payload max size 

                           o_regf_rd_en_mux_sel      <= SDR_SEL  ;
                           o_regf_rd_address_mux_sel <= SDR_SEL  ;
                           o_regf_wr_en_mux_sel      <= SDR_SEL  ;
                           o_scl_pp_od_mux_sel       <= SDR_SEL  ;
                           o_tx_en_mux_sel           <= SDR_SEL  ;
                           o_tx_mode_mux_sel         <= SDR_SEL  ;
                           o_rx_en_mux_sel           <= SDR_SEL  ;
                           o_rx_mode_mux_sel         <= SDR_SEL  ;
                           o_bit_cnt_en_mux_sel      <= SDR_SEL  ;
                           o_bit_rx_cnt_en_mux_sel   <= SDR_SEL  ;
                           o_fcnt_en_mux_sel         <= SDR_SEL  ;
                           o_scl_idle_mux_sel        <= SDR_SEL  ; 
                           state <= SDR_MODE;
                        end

                    else if (i_ibi_done)    
                        begin
                            o_ibi_en <= 1'b0 ;
                            state <= IDLE;
                        end     
                  end

             CTRL_REQ: begin
              if(i_crh_send_stop)
                begin
                  state               <= STOP ; 
                  o_tx_en             <= 1'b1      ;
                  o_tx_mode           <= 3'b010    ; //stop bit
                  o_pp_od             <= 1'b1      ; 
                  send_stop           <= 1'b1      ;
                  //o_scl_idle         <= 1'b0 ; 
                  o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                  o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                  o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                  o_scl_idle_mux_sel  <= I3C_ENGINE_SEL ;  
                end
              else if(i_crh_done)
                begin
                  state               <= IDLE ;
                  o_scl_pp_od_mux_sel <= I3C_ENGINE_SEL ;
                  o_tx_en_mux_sel     <= I3C_ENGINE_SEL ;
                  o_tx_mode_mux_sel   <= I3C_ENGINE_SEL ;
                  o_scl_idle_mux_sel  <= I3C_ENGINE_SEL ;  
                  o_crh_en            <= 1'b0 ;
                  o_pp_od             <= 1'b0           ; 
                end
                            
                        end
            


            ENTHDR: 
                begin
                    if (i_enthdr_done)
                        begin
                            o_hdrengine_en            <= 1'b1 ;          

                            o_sda_sel                 <= HDR_MODE_SEL   ; 

                            o_regf_rd_en_mux_sel      <= HDR_ENGINE_SEL ;             //(REG File) shared btw HDR & SDR
                            o_regf_rd_address_mux_sel <= HDR_ENGINE_SEL ;             //(REG File) shared btw HDR & SDR
                            o_regf_wr_en_mux_sel      <= HDR_ENGINE_SEL ;             //(REG File) shared btw HDR & SDR
                            o_scl_pp_od_mux_sel       <= HDR_ENGINE_SEL ;             //(SCL GEN) shared btw HDR & SDR
                           


                            //o_tx_en_mux_sel           <= HDR_ENGINE_SEL ;
                            // o_tx_mode_mux_sel        <= HDR_ENGINE_SEL ;
                           
                            //o_rx_en_mux_sel           <= I3C_ENGINE_SEL  ;            //TO Disable sdr rx 
             
                            //o_bit_cnt_en_mode_mux_sel <= HDR_ENGINE_SEL ;
                            //o_bit_cnt_en_mux_sel      <= HDR_ENGINE_SEL ;
                            //o_bit_rx_cnt_en_mux_sel   <= HDR_ENGINE_SEL ;
                            //o_fcnt_en_mux_sel         <= HDR_ENGINE_SEL ;
                            //o_scl_idle_mux_sel        <= HDR_ENGINE_SEL ;
                            

                            state                     <= HDR_ENGINE     ; 
                        end 

                    else
                        begin
                            state                     <= ENTHDR         ; 
                        end 
                end


            HDR_ENGINE:
               begin
                 if(i_hdrengine_exit)
                  begin
                    o_scl_pp_od_mux_sel           <= I3C_ENGINE_SEL ;
                    o_tx_en_mux_sel               <= I3C_ENGINE_SEL ;
                    o_tx_mode_mux_sel             <= I3C_ENGINE_SEL ;
                    o_scl_idle_mux_sel            <= I3C_ENGINE_SEL ;
                    o_bits_cnt_regf_rx_tx_sel     <= I3C_ENGINE_SEL  ;  
                    o_ser_rx_tx_mux_sel           <= I3C_ENGINE_SEL ; 
                    state                         <= STOP        ; 
                  end














               end
         endcase
            
        end
  end

endmodule

`default_nettype wire

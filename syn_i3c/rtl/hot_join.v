//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Yaseen Salah
// Revision: 
//
// Version : 1.1
// 
// Create Date:  8:56 PM     3/15/2023 
// Design Name:  hot_join
// Module Name:  hot_join 
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
module hot_join(
    //--inputs from system top
    input  wire          i_hot_join_clk                , //System Clock 50 MHz
    input  wire          i_hot_join_rst_n              , //System Active Low Reset

    //--inputs from i3c_engine
    input  wire          i_hot_join_enable             , //Hot-Join Enable-Signal
    input  wire          i_hot_join_ccc                , //Sending Hot-Join CCCs Request (if Host wanna ENHJ or DISHJ without prior HJ Request)

    //--inputs from reg_file
    input  wire          i_hot_join_support            , //CRCAP1[0] Hardcoded (read-only) [1 >> Supported , 0 >> Not Supported]
    input  wire  [2:0]   i_hot_join_configuration      , //HJ Configuration register {AVAL/BUSY , EN/DIS , ACK/NACK} (Host can overwrite at any time)

    //--inputs from controller_tx
    input  wire          i_hot_join_tx_mode_done       , //Tx Current Mode Done-Flag
    input  wire          i_hot_join_tx_pp_mode_done    , //Tx Current Mode Done-Flag for Push-Pull small periods

    //--inputs from controller_rx
    input  wire          i_hot_join_rx_mode_done       , //Rx Current Mode Done-Flag
    input  wire          i_hot_join_nack_ack           , //Rx Sampled Target' Acknowledgment [1 >> NACK , 0 >> ACK]

    //--inputs from scl_generation
    input  wire          i_hot_join_scl_neg_edge       , //SCL Falling-Edge Flag
    input  wire          i_hot_join_scl_pos_edge       , //SCL Rising-Edge Flag

    //--outputs to controller_tx
    output reg           o_hot_join_tx_en              , //Tx Enable-Flag
    output reg   [2:0]   o_hot_join_tx_mode            , //Tx Current Mode Selector

    //--outputs to controller_rx
    output reg           o_hot_join_rx_en              , //Rx Enable-Flag
    output reg   [2:0]   o_hot_join_rx_mode            , //Rx Current Mode Selector 

    //--outputs to reg_file
    output reg           o_hot_join_regf_rd_en         , //RegFile Read Enable-Flag
    output reg   [11:0]   o_hot_join_regf_addr         , //RegFile Read/Write Address           badr 

    //--outputs to bits_counter
    output reg           o_hot_join_cnt_en             , //Bits Counter Enable-Flag
    output reg           o_hot_join_pp_od              , //SDA Driving Selector [1 >> Push-Pull , 0 >> Open-Drain] (also output to "sda_handling" and "scl_generation")

    //--outputs to i3c_engine
    output reg           o_hot_join_daa_req            , //DAA Procedure Request (Suggestion: Trigger DAA directly for time optimization)
    output reg           o_hot_join_ctrl_role_pass     , //CRR Procedure Request (Suggestion: Trigger CRH directly for time optimization)
    output reg           o_hot_join_acc_rej            , //Hot-Join Request Accepted/Rejected flag [1 >> ACCEPTED , 0 >> REJECTED]
    output reg           o_hot_join_done                 //Hot-Join Block Done-Flag 

    );



//-- States in Gray-Encoding ---------------------------------------------

localparam HJ_IDLE            = 3'b000 ; 
localparam CTRL_ACK_BIT       = 3'b001 ;
localparam CTRL_NACK_BIT      = 3'b011 ;
localparam REPEATED_START_BIT = 3'b010 ;
localparam CCC_ADDRESS        = 3'b110 ;
localparam TRGT_ACK_BIT       = 3'b111 ;
localparam CCC_DATA           = 3'b101 ;
localparam PARITY_BIT         = 3'b100 ;

//-- CCCs Modes  ---------------------------------------------------------

localparam ENHJ_MODE  = 1'b1 ;
localparam DISHJ_MODE = 1'b0 ;

//-- internal wires declaration ------------------------------------------

reg [2:0] state                  ;
reg       second_frame_done      ;
reg       hot_join_cfg_ack_nack  ; //HJ Configuration register [1 >> ACK HJ   ] , [0 >> NACK HJ   ]
reg       hot_join_cfg_en_dis    ; //HJ Configuration register [1 >> Enable HJ] , [0 >> Disable HJ]
reg       hot_join_cfg_aval_busy ; //HJ Configuration register [1 >> Available] , [0 >> Busy      ] //for DAA or CR-Pass procedures


always @(posedge i_hot_join_clk or negedge i_hot_join_rst_n) 
    begin: hot_join_controller_fsm
        if (!i_hot_join_rst_n) 
            begin
                o_hot_join_tx_en          <= 1'b0                         ;
                o_hot_join_tx_mode        <= 3'b0                         ;
                o_hot_join_rx_en          <= 1'b0                         ;
                o_hot_join_rx_mode        <= 2'b0                         ;
                o_hot_join_regf_rd_en     <= 1'b0                         ;
                o_hot_join_regf_addr      <= 10'd0                        ;
                o_hot_join_cnt_en         <= 1'b0                         ;
                o_hot_join_pp_od          <= 1'b0                         ;
                o_hot_join_daa_req        <= 1'b0                         ;
                o_hot_join_ctrl_role_pass <= 1'b0                         ;
                o_hot_join_acc_rej        <= 1'b0                         ;
                o_hot_join_done           <= 1'b0                         ;
                second_frame_done         <= 1'b0                         ;
                //preventing glitching or configuration-changing during sending CCCs
                hot_join_cfg_ack_nack     <= i_hot_join_configuration[0] ;
                hot_join_cfg_en_dis       <= i_hot_join_configuration[1] ;
                hot_join_cfg_aval_busy    <= i_hot_join_configuration[2] ;
                state <= HJ_IDLE ;
            end
        else 
            begin
                case (state)
                HJ_IDLE:
                    begin
                        o_hot_join_tx_en          <= 1'b0                         ;
                        o_hot_join_tx_mode        <= 3'b0                         ;
                        o_hot_join_rx_en          <= 1'b0                         ;
                        o_hot_join_rx_mode        <= 2'b0                         ;
                        o_hot_join_regf_rd_en     <= 1'b1                         ; //early reg_file setup as the 7'h7E is the first reg being read
                        o_hot_join_regf_addr      <= 10'd46                       ; 
                        o_hot_join_cnt_en         <= 1'b0                         ;
                        o_hot_join_pp_od          <= 1'b0                         ;
                        o_hot_join_daa_req        <= 1'b0                         ;
                        o_hot_join_ctrl_role_pass <= 1'b0                         ;
                        o_hot_join_acc_rej        <= 1'b0                         ;
                        o_hot_join_done           <= 1'b0                         ;
                        second_frame_done         <= 1'b0                         ;
                        //preventing glitching or configuration-changing during sending CCCs
                        hot_join_cfg_ack_nack     <= i_hot_join_configuration[0] ;
                        hot_join_cfg_en_dis       <= i_hot_join_configuration[1] ;
                        hot_join_cfg_aval_busy    <= i_hot_join_configuration[2] ;

                        if (i_hot_join_enable)
                            begin
                                if (i_hot_join_ccc)
                                    begin
                                        o_hot_join_regf_addr  <= 10'd46      ; //BROADCAST ADDRESS (7h'7E/W)
                                        o_hot_join_regf_rd_en <= 1'b1        ;
                                        o_hot_join_tx_en      <= 1'b1        ;
                                        o_hot_join_pp_od      <= 1'b0        ; //open-drain
                                        o_hot_join_tx_mode    <= 3'b001      ; //SERIALIZING Mode
                                        state                 <= CCC_ADDRESS ; //supposing that i3c_control_unit initiated START before hot_join_enable
                                    end
                                else if (!i_hot_join_support || !hot_join_cfg_ack_nack)
                                    begin
                                        o_hot_join_acc_rej    <= 1'b0          ; //HJ IS REJECTED
                                        o_hot_join_regf_rd_en <= 1'b0          ;
                                        o_hot_join_tx_en      <= 1'b1          ;
                                        o_hot_join_pp_od      <= 1'b1          ; //push-pull
                                        o_hot_join_tx_mode    <= 3'b101        ; //CTRL_NACK Mode (High-Z)
                                        o_hot_join_cnt_en     <= 1'b0          ; //Disable Bits Counter
                                        state                 <= CTRL_NACK_BIT ;
                                    end
                                else
                                    begin
                                        o_hot_join_acc_rej    <= 1'b1         ; //HJ IS ACCEPTED
                                        o_hot_join_regf_rd_en <= 1'b0         ;
                                        o_hot_join_pp_od      <= 1'b1         ; //push-pull
                                        o_hot_join_tx_en      <= 1'b1         ;
                                        o_hot_join_tx_mode    <= 3'b111       ; //CTRL_ACK Mode
                                        o_hot_join_cnt_en     <= 1'b0         ; //Disable Bits Counter
                                        state                 <= CTRL_ACK_BIT ;
                                    end
                            end
                        else 
                            begin
                                state <= HJ_IDLE ;
                            end
                    end

                CTRL_ACK_BIT:
                    begin
                        if (i_hot_join_tx_mode_done)
                            begin
                                if (!hot_join_cfg_en_dis)  //controller may DISHJ after ACK
                                    begin
                                        o_hot_join_tx_en   <= 1'b1               ;
                                        o_hot_join_pp_od   <= 1'b1               ; //push-pull
                                        o_hot_join_tx_mode <= 3'b110             ; //REPEATED_START Mode
                                        o_hot_join_cnt_en  <= 1'b0               ; //Disable Bits Counter
                                        o_hot_join_done    <= 1'b0               ;
                                        state              <= REPEATED_START_BIT ; //starting DISHJ CCC 
                                    end
                                else 
                                    begin
                                        o_hot_join_tx_en <= 1'b0 ;

                                        o_hot_join_pp_od <= 1'b0 ;
                                        state <= HJ_IDLE ; 
                                        o_hot_join_done <= 1'b1 ; 
                                        if (hot_join_cfg_aval_busy)
                                            begin
                                                o_hot_join_daa_req <= 1'b1 ;  //DAA will initiate Sr and cont. the flow
                                            end
                                    end
                            end   
                        else
                            begin
                                state <= CTRL_ACK_BIT ;
                            end
                    end  

                CTRL_NACK_BIT:
                    begin
                        if (i_hot_join_tx_mode_done)
                            begin
                            //NACK and DISHJ path
                                if (!hot_join_cfg_en_dis || !i_hot_join_support) 
                                    begin
                                        o_hot_join_tx_en   <= 1'b1               ;
                                        o_hot_join_pp_od   <= 1'b1               ; //push-pull
                                        o_hot_join_tx_mode <= 3'b110             ; //REPEATED_START Mode
                                        o_hot_join_cnt_en  <= 1'b0               ; //Disable Bits Counter
                                        o_hot_join_done    <= 1'b0               ;
                                        state              <= REPEATED_START_BIT ; //starting DISHJ CCC
                                    end
                            //NACK only path
                                else                        
                                    begin
                                        state <= HJ_IDLE ;  
                                        o_hot_join_done <= 1'b1 ;
                                    end 
                            end   
                        else
                            begin
                                state <= CTRL_NACK_BIT ;
                            end
                    end  

                REPEATED_START_BIT:  //only for ENEC/DISEC paths
                    begin
                        if (i_hot_join_tx_mode_done)
                            begin
                                o_hot_join_tx_en      <= 1'b1        ;
                                o_hot_join_pp_od      <= 1'b1        ; //push-pull
                                o_hot_join_tx_mode    <= 3'b001      ; //SERIALIZING Mode
                                o_hot_join_cnt_en     <= 1'b1        ; //Enable Bits Counter
                                o_hot_join_regf_addr  <= 10'd46      ; //BROADCAST ADDRESS (7h'7E/W)
                                o_hot_join_regf_rd_en <= 1'b1        ;
                                state                 <= CCC_ADDRESS ;
                            end   
                        else
                            begin
                                o_hot_join_tx_en   <= 1'b1               ;
                                o_hot_join_pp_od   <= 1'b1               ; //push-pull
                                o_hot_join_tx_mode <= 3'b110             ; //REPEATED_START Mode
                                o_hot_join_cnt_en  <= 1'b0               ; //Disable Bits Counter
                                o_hot_join_done    <= 1'b0               ;
                                state              <= REPEATED_START_BIT ;
                            end
                    end 

                CCC_ADDRESS:  //sending BROADCAST ADDRESS
                    begin
                        o_hot_join_cnt_en     <= 1'b1 ; //Enable Bits Counter
                        o_hot_join_regf_rd_en <= 1'b0 ;
                        if (i_hot_join_tx_pp_mode_done)
                            begin
                                o_hot_join_pp_od   <= 1'b0         ; //open-drain
                                o_hot_join_cnt_en  <= 1'b0         ; //Disable Bits Counter
                                o_hot_join_tx_en   <= 1'b0         ;
                                o_hot_join_tx_mode <= 3'b000       ;
                                o_hot_join_rx_en   <= 1'b1         ;
                                o_hot_join_rx_mode <= 3'b000       ; //ACK Mode
                                state              <= TRGT_ACK_BIT ;
                            end   
                        else
                            begin
                                state <= CCC_ADDRESS ;
                            end
                    end 

                TRGT_ACK_BIT:
                    begin
                        o_hot_join_regf_rd_en <= 1'b1 ; //early reg_file setup for timing optimization
                        case (hot_join_cfg_en_dis)
                        ENHJ_MODE : o_hot_join_regf_addr <= 10'd401 ; //ENEC CCC (0x00)
                        DISHJ_MODE: o_hot_join_regf_addr <= 10'd403 ; //DISEC CCC (0x01)
                        endcase 
                        if (i_hot_join_rx_mode_done && i_hot_join_scl_neg_edge)
                            begin
                                if (!i_hot_join_nack_ack)
                                    begin
                                        state <= CCC_DATA ;
                                        o_hot_join_tx_en          <= 1'b1   ;
                                        o_hot_join_rx_en          <= 1'b0   ;
                                        o_hot_join_pp_od          <= 1'b1   ; //push-pull
                                        o_hot_join_tx_mode        <= 3'b001 ; //SERIALIZING Mode
                                        o_hot_join_cnt_en         <= 1'b1   ; //Enable Bits Counter
                                    end
                                else
                                    begin
                                        state <= HJ_IDLE ; //STOP after NACK
                                        o_hot_join_done    <= 1'b1 ;
                                        o_hot_join_acc_rej <= 1'b0 ;
                                    end
                            end   
                        else
                            begin
                                state <= TRGT_ACK_BIT ;
                            end
                    end 

                CCC_DATA:
                    begin
                        o_hot_join_regf_rd_en <= 1'b0 ;
                        if (i_hot_join_tx_pp_mode_done)
                            begin
                                state <= PARITY_BIT ;
                                o_hot_join_tx_en   <= 1'b1   ;
                                o_hot_join_pp_od   <= 1'b1   ; //push-pull
                                o_hot_join_tx_mode <= 3'b011 ; //PARITY Mode
                                o_hot_join_cnt_en  <= 1'b0   ; //Disable Bits Counter
                            end   
                        else
                            begin
                                state <= CCC_DATA ;
                            end
                    end 
                    
                PARITY_BIT:
                    begin
                        o_hot_join_regf_rd_en <= 1'b1 ; //early reg_file setup for second_frame optimization
                        case (hot_join_cfg_en_dis) 
                        ENHJ_MODE : o_hot_join_regf_addr <= 10'd402 ; //ENEC BYTE
                        DISHJ_MODE: o_hot_join_regf_addr <= 10'd404 ; //DISEC BYTE
                        endcase
                        if (i_hot_join_tx_pp_mode_done)
                            begin
                                if (!second_frame_done)
                                    begin
                                        state <= CCC_DATA ;
                                        o_hot_join_tx_en   <= 1'b1   ;
                                        o_hot_join_pp_od   <= 1'b1   ; //push-pull
                                        o_hot_join_tx_mode <= 3'b001 ; //SERIALIZING Mode
                                        o_hot_join_cnt_en  <= 1'b1   ; //Enable Bits Counter
                                        second_frame_done  <= 1'b1   ;
                                    end
                                else
                                    begin
                                        state <= HJ_IDLE ;
                                        second_frame_done  <= 1'b0   ;
                                        o_hot_join_tx_mode <= 3'b010 ; //STOP Mode for a smooth mux select with i3c_engine
                                        o_hot_join_done    <= 1'b1   ;
                                        if (!i_hot_join_support && hot_join_cfg_aval_busy)
                                            begin
                                                o_hot_join_ctrl_role_pass <= 1'b1 ;  //i3c_main_controller will enable CRH
                                            end
                                    end
                            end   
                        else
                            begin
                                state <= PARITY_BIT ;
                            end                        
                    end 
                endcase    

                if (!i_hot_join_enable)
                    begin
                        state <= HJ_IDLE ; //supporting immediate hj_disable for all states
                    end            
            end
    end



endmodule

`default_nettype wire
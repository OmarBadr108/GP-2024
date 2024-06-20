//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Yaseen Salah , Nour Eldeen Samir
// Revision: 
//
// Version : 2.0
// 
// Create Date:  7:46 PM     29/3/2023 
// Design Name:  I2C Legacy Mode
// Module Name:  i2c_legacy_mode 
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
module i2c_legacy_mode(
    input  wire          i_clk                  , //System Clock 50 MHz
    input  wire          i_rst_n                , //System Active Low Reset
    input  wire          i_i2c_mode_en          , //I2C Legacy Mode Enable-Flag from I3C Engine
    input  wire          i_last_frame           , //Last Frame Flag from Frame Counter
    input  wire          i_tx_mode_done         , //Tx Current Mode Done-Flag 
    input  wire          i_rx_mode_done         , //Rx Current Mode Done-Flag
    input  wire          i_regf_rx_tx           , //RnW from RegFile 1 >> Rx , 0 >> Tx 
    input  wire          i_rx_nack_ack          , // 1 >> NACK , 0 >> ACK 
    input  wire          i_rx_arbitration_lost  ,
    input  wire          i_scl_neg_edge         ,
    input  wire          i_scl_pos_edge         , 
    output reg           o_frame_cnt_en         , //Frames Counter Enable-Flag
    output reg           o_bit_cnt_en           , //Bits Counter Enable-Flag
    output reg           o_bit_rx_cnt_en        , //Bits Counter Enable-Flag for Rx Deserializing (DATA_IN)
    output reg           o_tx_en                , //Tx Enable-Flag
    output reg   [2:0]   o_tx_mode              , //Tx Current Mode Selector
    output reg           o_rx_en                , //Rx Enable-Flag
    output reg   [2:0]   o_rx_mode              , //Rx Current Mode Selector
    output reg           o_pp_od                , //Push-Pull/Open-Drain Selector (Always = 0 in I2C)
    output reg           o_regf_rd_en           , //RegFile Read Enable-Flag
    output reg   [11:0]   o_regf_addr            , //RegFile Read/Write Address
    output reg           o_rx_data_valid        , //Received Data Valid-Flag for Host Interface
    output reg           o_target_nack          , //Error-Flag for I3C Engine (Target doesn't ACK)
    output reg           o_i2c_mode_done          //I2C Legacy Mode Done-Flag for I3C Engine
    );


//-- states encoding in gray --------------------------------------------

localparam I2C_IDLE         = 3'b000 ; 
localparam ADDRESS          = 3'b001 ;
localparam TRGT_ACK         = 3'b011 ;
localparam DATA_OUT         = 3'b010 ;
localparam CTRL_ACK         = 3'b110 ;
localparam DATA_IN          = 3'b111 ;


//-- internal wires declaration -----------------------------------------

reg [2:0] state         ;
reg       addr_data_ack ;  //Flag to state whether the TRGT_ACK is coming after ADDRESS or DATA_OUT
reg       i2c_mode_en_prev ;  


//-- i2c legacy mode fsm ------------------------------------------------

always @(posedge i_clk or negedge i_rst_n) 
    begin
    if (!i_rst_n) 
        begin
            o_frame_cnt_en  <= 1'b0      ;
            o_bit_cnt_en    <= 1'b0      ;
            o_bit_rx_cnt_en <= 1'b0      ;
            o_tx_en         <= 1'b0      ;
            o_tx_mode       <= 3'b000    ;
            o_rx_en         <= 1'b0      ;
            o_rx_mode       <= 2'b00     ;
            o_pp_od         <= 1'b0      ;
            o_regf_rd_en    <= 1'b0      ;
            o_regf_addr     <= 12'b000000 ;   
            o_rx_data_valid <= 1'b0      ;
            o_target_nack   <= 1'b1      ;  
            o_i2c_mode_done <= 1'b0      ;
            addr_data_ack   <= 1'b0      ;  
            i2c_mode_en_prev <= 1'b1     ; 
            state           <= I2C_IDLE  ;   
        end
    else
        begin
            if (!i_i2c_mode_en)
                begin
                    state <= I2C_IDLE ; //supporting immediate i2c_disable for all states
                end
            case (state)
            I2C_IDLE:
                begin
                    o_frame_cnt_en  <= 1'b0      ;
                    //o_bit_cnt_en    <= 1'b0      ;
                    //o_bit_rx_cnt_en <= 1'b0      ;
                    o_tx_en         <= 1'b0      ;
                    o_tx_mode       <= 3'b000    ;
                    o_rx_en         <= 1'b1      ; // as we need it enabled at arbitration
                    o_pp_od         <= 1'b0      ;
                    o_regf_rd_en    <= 1'b0      ;
                    //o_regf_addr     <= 6'b000000 ;   
                    o_rx_data_valid <= 1'b0      ;  
                    o_target_nack   <= 1'b1      ; 
                    o_i2c_mode_done <= 1'b0      ;
                    addr_data_ack   <= 1'b0      ; 
                    i2c_mode_en_prev <= i_i2c_mode_en ;  

                    if (i_i2c_mode_en && !i2c_mode_en_prev ) 
                        begin
                            o_bit_cnt_en    <= 1'b1      ;
                            o_tx_en         <= 1'b1      ;
                            o_tx_mode       <= 3'b001    ; //SERIALIZING MODE
                            o_regf_rd_en    <= 1'b1      ;
                            o_regf_addr     <= 12'b000000 ;  //TBD After Register File Locations Management

                            //// Arbitration signals //////
                            o_rx_en         <= 1'b1      ; 
                            o_rx_mode       <= 2'b10     ; // ARBITRATION mode
                            state           <= ADDRESS   ;
                        end
                    else 
                        begin
                            state <= I2C_IDLE ;
                        end
                end
            ADDRESS:
                begin
                    o_regf_rd_en <= 1'b0 ;

                    if (i_tx_mode_done && i_scl_neg_edge)
                        begin
                            o_bit_cnt_en    <= 1'b0      ;
                            o_tx_en         <= 1'b0      ;
                            o_tx_mode       <= 3'b000    ;
                            o_rx_en         <= 1'b1      ;
                            o_rx_mode       <= 2'b00     ; //ACK MODE
                            addr_data_ack   <= 1'b1      ; //Acknowledge to Address
                            state           <= TRGT_ACK  ;
                        end
                    else if (i_rx_arbitration_lost)
                      begin 
                        o_i2c_mode_done <= 1'b1        ;
                        o_regf_addr     <= 'd48        ;
                        state           <=  I2C_IDLE   ;
                     end
                     else
                        begin
                            state <= ADDRESS ;
                        end
                end
            TRGT_ACK:
                begin
                    if (i_rx_mode_done && i_scl_neg_edge)
                        begin
                            o_frame_cnt_en  <= 1'b1 ;
                            o_bit_cnt_en    <= 1'b1 ;
                            if (i_rx_nack_ack)
                                begin
                                    o_frame_cnt_en  <= 1'b0     ;
                                    o_bit_cnt_en    <= 1'b0     ;
                                    o_tx_en         <= 1'b0     ;
                                    o_tx_mode       <= 3'b000   ;
                                    o_rx_en         <= 1'b0     ;
                                    o_rx_mode       <= 2'b00    ;
                                    o_target_nack   <= 1'b1     ;
                                    o_i2c_mode_done <= 1'b1     ;
                                    state           <= I2C_IDLE ; 
                                end
                            else 
                                begin
                                    if (addr_data_ack)  //TRGT_ACK AFTER ADDRESS
                                        begin
                                            if (i_regf_rx_tx)
                                                begin
                                                    o_tx_en         <= 1'b0      ;
                                                    o_tx_mode       <= 3'b000    ;
                                                    o_rx_en         <= 1'b1      ;
                                                    o_rx_mode       <= 2'b01     ; //DESERIALIZING MODE
                                                    o_bit_rx_cnt_en <= 1'b1      ; //Counting under Rx Conditions
                                                    o_regf_addr     <= 12'b010011 ; // 1st frame to be written in RegFile at index 19 
                                                    state           <= DATA_IN   ; 
                                                end
                                            else
                                                begin
                                                    o_tx_en      <= 1'b1      ;
                                                    o_tx_mode    <= 3'b001    ; //SERIALIZING MODE
                                                    o_rx_en      <= 1'b0      ;
                                                    o_rx_mode    <= 2'b00     ;
                                                    o_regf_rd_en <= 1'b1      ;
                                                    o_regf_addr  <= 12'b000010 ; // 1st frame of data in RegFile at index 2.
                                                    state        <= DATA_OUT  ;
                                                end                            
                                        end
                                    else                //TRGT_ACK AFTER DATA_OUT
                                        begin
                                            if (i_last_frame)
                                                begin
                                                    o_frame_cnt_en  <= 1'b0               ;
                                                    o_bit_cnt_en    <= 1'b0               ;
                                                    o_tx_en         <= 1'b0               ;
                                                    o_tx_mode       <= 3'b000             ;
                                                    o_rx_en         <= 1'b0               ;
                                                    o_rx_mode       <= 2'b00              ;
                                                    o_i2c_mode_done <= 1'b1               ;
                                                    state           <= I2C_IDLE           ; 
                                                end
                                            else
                                                begin
                                                    o_tx_en         <= 1'b1               ;
                                                    o_tx_mode       <= 3'b001             ; //SERIALIZING MODE
                                                    o_rx_en         <= 1'b0               ;
                                                    o_rx_mode       <= 2'b00              ;
                                                    o_regf_rd_en    <= 1'b1               ;
                                                    o_regf_addr     <= o_regf_addr + 1'b1 ;
                                                    state           <= DATA_OUT           ;
                                                end                            
                                        end
                                end
                        end
                    else
                        begin
                            state <= TRGT_ACK ;
                        end
                end
            DATA_OUT:
                begin
                    o_regf_rd_en <= 1'b0 ;
                    if (i_tx_mode_done && i_scl_neg_edge)
                        begin
                            o_frame_cnt_en  <= 1'b0     ;
                            o_bit_cnt_en    <= 1'b0     ;
                            o_tx_en         <= 1'b0     ;
                            o_tx_mode       <= 3'b000   ;
                            o_rx_en         <= 1'b1     ;
                            o_rx_mode       <= 2'b00    ; //ACK MODE
                            addr_data_ack   <= 1'b0     ; //Acknowledge to Wr_Data
                            state           <= TRGT_ACK ;
                        end
                    else
                        begin
                            state <= DATA_OUT ;
                        end
                end
            DATA_IN:
                begin
                    if (i_rx_mode_done && i_scl_neg_edge)
                        begin
                            o_frame_cnt_en  <= 1'b0     ;
                            o_bit_cnt_en    <= 1'b0     ;
                            o_tx_en         <= 1'b1     ;
                            case (i_last_frame)
                            1'b0: o_tx_mode <= 3'b111   ; //CTRL_ACK MODE
                            1'b1: o_tx_mode <= 3'b101   ; //CTRL_NACK MODE
                            endcase
                            o_rx_en         <= 1'b0     ;
                            o_rx_mode       <= 2'b00    ;
                            addr_data_ack   <= 1'b0     ;
                            state           <= CTRL_ACK ;
                            o_rx_data_valid <= 1'b1 ;
                        end
                    else
                        begin
                            state <= DATA_IN ;
                        end  
                end
            CTRL_ACK:
                begin

                    o_rx_data_valid <= 1'b0 ;
                    if (i_tx_mode_done && i_scl_neg_edge )

                        begin
                            if (i_last_frame)
                                begin
                                    o_frame_cnt_en  <= 1'b0               ;
                                    o_bit_cnt_en    <= 1'b0               ;
                                    o_tx_en         <= 1'b0               ;
                                    o_tx_mode       <= 3'b000             ;
                                    o_rx_en         <= 1'b0               ;
                                    o_rx_mode       <= 2'b00              ;
                                    o_i2c_mode_done <= 1'b1               ;
                                    state           <= I2C_IDLE           ; 
                                end
                            else
                                begin
                                    o_frame_cnt_en  <= 1'b1               ;
                                    o_bit_cnt_en    <= 1'b1               ;
                                    o_bit_rx_cnt_en <= 1'b1               ; //Counting under Rx Conditions
                                    o_tx_en         <= 1'b0               ;
                                    o_tx_mode       <= 3'b000             ;
                                    o_rx_en         <= 1'b1               ;
                                    o_rx_mode       <= 2'b01              ; //DESERIALIZING MODE
                                    o_regf_addr     <= o_regf_addr + 1'b1 ;
                                    state           <= DATA_IN            ;
                                end  
                        end
                    else
                        begin
                            state <= CTRL_ACK ;
                        end    
                end
            endcase
        end
    end

endmodule

`default_nettype wire

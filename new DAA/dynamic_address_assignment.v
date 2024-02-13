////////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Youssef Noeman
// Revision: 
//
// Version : 1.0
// 
// Create Date:  4:00 PM     27/2/2023 
// Design Name:  i3c_controller
// Module Name:  dynamic_address_assignment
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
module dynamic_address_assignment (
    input  wire          i_daa_clk                    ,
    input  wire          i_daa_rst_n                  ,
    input  wire          i_mcu_daa_en                 , // enable from main ctrl unit 
    input  wire          i_scl_daa_pos_edge           , // SCL POS EDGE
    input  wire          i_scl_daa_neg_edge           , // SCL NEG EDGE
    input  wire          i_tx_daa_mode_done           , // TX MODE DONE
    input  wire          i_tx_daa_done                , // TX MODE DONE IN CASE OF 7-bit SERIALIZING  
    input  wire          i_rx_daa_mode_done           , // RX MODE DONE
    input  wire          i_rx_daa_nack_ack            , // 1:NACK      , 0: ACK
    output wire          o_daa_pp_od                  , // 1: pushpull , 0: opendrain
    output reg           o_daa_regf_rd_en             , // Reg_file read enable
    output reg           o_daa_regf_wr_en             , // Reg_file write enable
    output reg  [7:0]    o_daa_regf_data_wr           , // Reg_file data write
    output reg  [9:0]    o_daa_regf_addr              , // Reg_file Address
    output reg  [2:0]    o_daa_tx_mode                , // TX configuration
    output reg           o_daa_tx_en                  , // TX enable
    output reg  [2:0]    o_daa_rx_mode                , // RX configuration 
    output reg           o_daa_rx_en                  , // RX enable
    output reg           o_daa_fcnt_en                , // Frame Counter Enable
    output reg  [7:0]    o_daa_fcnt_no_frms           , // No of frames to Frame counter
    output reg           o_daa_bits_cnt_en            , // Bits Counter Enable
    output reg           o_daa_rx_cnt_en              , // bits counter rx enable in case of read data
    output reg           o_daa_error                  , // error management procedure
    output reg           o_regf_wr_data_mux_sel       , // MUX SELECTOR FOR REGFILE DATA WRITE
    output reg           o_daa_mcu_done              ); // procedure done

//---------------------------------- states encoding in gray ----------------------------------------------
localparam DAA_IDLE                     = 4'b0000 ; // 0
localparam START                        = 4'b0001 ; // 1
localparam ENTDAA                       = 4'b0011 ; // 3
localparam READ_DATA                    = 4'b0010 ; // 2
localparam DAA                          = 4'b0110 ; // 6
localparam FINISH                       = 4'b0111 ; // 7
localparam BROADCAST                    = 4'b0100 ; // 4
localparam PARITY                       = 4'b1100 ; // C
localparam ACK                          = 4'b1101 ; // D

//---------------------------------- Paramaters needed ----------------------------------------------------

localparam first_address                = 7'h08   ;
localparam base_address_of_regf         =  'd200  ;

//---------------------------------- Assign Statements ----------------------------------------------------

assign o_daa_pp_od = 1'b0        ; // dynamic address assignment procedure is always opendrain // must be registered

//---------------------------------- INTERNAL WIRES -------------------------------------------------------

reg [3:0] state                  ;
reg [2:0] frames_count           ; // incrementing by 1 with each mode done in case of READ_DATA (DESERIALIZING) 
reg [5:0] addresses_count        ; // used in address assignment to increment the assigned address  
reg [7:0] target_offset          ; // to calculate regf address pointer
reg [1:0] nacks_counter          ; // to determine how many nacks by the target
reg       par_to_ack             ; //PARITY TO ACKNOWLEDGE INDICATOR, NOT BROADCAST READ TO ACK
reg       ccc_to_par             ; // CCC TO PAR INDICATOR, NOT DATA TO PARITY
reg       daa_mode               ; //ENTDAA IS SENT // any start after is a REPEATED START, and any broadcast is READ.

//---------------------------------- DAA MAIN FSM  --------------------------------------------------------

always @(posedge i_daa_clk or negedge i_daa_rst_n)
    begin: daa_mode_fsm
        
        if (!i_daa_rst_n)
            begin
                state                   <= DAA_IDLE; //idle state after reset  
                target_offset           <= 8'b0;
                nacks_counter           <= 2'b0; 
                frames_count            <= 3'b0;
                par_to_ack              <= 1'b0;
                ccc_to_par              <= 1'b0;
                daa_mode                <= 1'b0;
                o_daa_regf_rd_en        <= 1'b0;  
                o_daa_regf_wr_en        <= 1'b0;
                o_daa_regf_data_wr      <= 8'b0;
                o_daa_regf_addr         <= 10'b0;
                o_daa_tx_mode           <= 3'b0;
                o_daa_tx_en             <= 1'b0;
                o_daa_mcu_done          <= 1'b0;
                o_daa_rx_en             <= 1'b0;
                o_daa_rx_mode           <= 2'b00;
                o_daa_fcnt_en           <= 1'b0;
                o_daa_fcnt_no_frms      <= 8'b0;
                o_daa_bits_cnt_en       <= 1'b0;
                o_daa_error             <= 1'b0;
                o_regf_wr_data_mux_sel  <= 1'b0; 
            end          
        else
            begin
                case(state)
                    DAA_IDLE:
                        begin                        
                          if (i_mcu_daa_en)
                            begin
                              state <= BROADCAST;
                              target_offset           <= 8'b0;
                              nacks_counter           <= 2'b0; 
                              frames_count            <= 3'b0;
                              par_to_ack              <= 1'b0;
                              ccc_to_par              <= 1'b0;
                              daa_mode                <= 1'b0;
                              o_daa_mcu_done          <= 1'b0;
                              o_daa_rx_en             <= 1'b1;
                              o_daa_rx_mode           <= 2'b10;
                              o_daa_fcnt_en           <= 1'b0;
                              o_daa_fcnt_no_frms      <= 8'b0;
                              o_daa_bits_cnt_en       <= 1'b0;
                              o_daa_error             <= 1'b0;
                              o_regf_wr_data_mux_sel  <= 1'b0; 
                              o_daa_bits_cnt_en       <= 1'b1;
                            end
                          else
                            begin
                              state <= DAA_IDLE;
                            end                               
                        end
                    START:
                        begin

                            o_daa_rx_mode           <= 2'b10;   // 2024



                            o_daa_regf_rd_en        <= 1'b0;
                            o_daa_regf_wr_en        <= 1'b0;
                            o_daa_regf_data_wr      <= 8'b0;
                            o_daa_tx_mode           <= 3'b000;
                            o_daa_tx_en             <= 1'b1;    
                            if (i_scl_daa_neg_edge && i_tx_daa_mode_done)
                              begin
                                state <= BROADCAST;
                              end
                            else
                              begin
                                state <= START;
                              end                               
                        end
                    BROADCAST:
                        begin
                            //SERIALIZING DONE. NEXT STATE LOGIC
                            if (i_scl_daa_neg_edge && i_tx_daa_mode_done) 
                                begin
                                  state <= ACK; 
                                  o_daa_tx_en             <= 1'b0;
                                  o_daa_rx_en             <= 1'b1;
                                  o_daa_rx_mode           <= 2'b00;  // 2024 : wdy el RX le ACK state
                                end
                            else
                                begin
                                  state <= BROADCAST;
                                end 
                            // CHOOSING WHICH BROADCAST TO SERIALIZE. OUTPUT LOGIC     
                            if(daa_mode) 
                                begin
                                    o_daa_regf_rd_en        <= 1'b1; 
                                    o_daa_regf_wr_en        <= 1'b0; 
                                    o_daa_regf_data_wr      <= 8'b0; 
                                    o_daa_regf_addr         <= 10'b0000101111; // 47 decimal 
                                    o_daa_tx_mode           <= 3'b001;
                                    o_daa_tx_en             <= 1'b1;   
                                    o_daa_bits_cnt_en       <= 1'b1;                              
                                end
                            else
                                begin
                                    o_daa_regf_rd_en        <= 1'b1; 
                                    o_daa_regf_wr_en        <= 1'b0; 
                                    o_daa_regf_data_wr      <= 8'b0; 
                                    o_daa_regf_addr         <= 10'b0000101110; //46 decimal 
                                    o_daa_tx_mode           <= 3'b001;
                                    o_daa_tx_en             <= 1'b1;
                                    o_daa_bits_cnt_en       <= 1'b1; 
                                end                                                      
                        end 
                    ACK: //REVISE CODE APPROACH
                        begin
                        o_daa_bits_cnt_en       <= 1'b0;
                            //STATE TRANSITION CONDITION
                            if(i_rx_daa_mode_done && i_scl_daa_neg_edge)
                                begin
                                    // ACKNOWLEDGE INSIDE DAA MODE (WITHOUT HANDOFF)
                                    if(daa_mode)
                                        begin
                                            // ACKNOWLEDGE AFTER PARITY
                                            if(par_to_ack)
                                                begin                
                                                    if(i_rx_daa_nack_ack) //NACK AFTER PARITY OF ASSIGNED ADDRESS ----------- 2024 note : 1 for NACK 0 for ACK
                                                        begin
                                                            nacks_counter      <= nacks_counter + 1'b1;
                                                            if(nacks_counter == 2'b10)
                                                                begin
                                                                    o_daa_error <= 1'b1;
                                                                    o_daa_mcu_done <= 1'b1;
                                                                    state <= DAA_IDLE;    
                                                                end
                                                            else
                                                                begin
                                                                    o_daa_error <= 1'b0;
                                                                    state <= START;                                                                 
                                                                end                                                            
                                                        end  
                                                    else //ACK AFTER PARITY OF ASSIGNED ADDRESS
                                                        begin
                                                            nacks_counter <= 2'b0; 
                                                            state <= START;
                                                            // Logic to calculate target offset that determines the regf pointer
                                                            if(addresses_count == 6'b0)
                                                                begin    
                                                                    target_offset           <= 'd9;
                                                                    addresses_count         <= addresses_count + 1;
                                                                end
                                                            else
                                                                begin
                                                                    target_offset           <= target_offset + 'd9;
                                                                    addresses_count         <= addresses_count + 1;
                                                                end    
                                                        end                                                 
                                                end
                                            // ACKNOWLEDGE AFTER BROADCAST READ    
                                            else
                                                begin
                                                    if(!i_rx_daa_nack_ack) //ACK AFTER BROADCAST READ
                                                        begin
                                                            state <= READ_DATA;
                                                            o_daa_regf_rd_en        <= 1'b0; 
                                                            o_daa_regf_wr_en        <= 1'b1; 
                                                            o_daa_regf_addr         <= base_address_of_regf + target_offset; 
                                                            o_daa_tx_en             <= 1'b0;    
                                                            o_daa_rx_mode           <= 2'b01;                                                                               
                                                            o_daa_rx_en             <= 1'b1;
                                                            o_daa_fcnt_en           <= 1'b1;
                                                            o_daa_fcnt_no_frms      <= 8'b1000;
                                                            o_daa_bits_cnt_en       <= 1'b1;
                                                        end   
                                                    else //NACK AFTER BROADCAST READ
                                                        begin
                                                            state <= FINISH;
                                                        end
                                                end
                                        end
                                    // ACKNOWLEDGE OUTSIDE DAA MDOE, AFTER BROADCAST WRITE (WITH HANDOFF)   
                                    else
                                        begin
                                            if (!i_rx_daa_nack_ack) //IF ACK, NEXT STATE IS ENTDAA
                                                begin
                                                    state <= ENTDAA;
                                                    o_daa_regf_rd_en        <= 1'b1; 
                                                    o_daa_regf_wr_en        <= 1'b0; 
                                                    o_daa_regf_data_wr      <= 8'b0; 
                                                    o_daa_regf_addr         <=  'd49; 
                                                    o_daa_tx_mode           <= 3'b001;
                                                    o_daa_tx_en             <= 1'b1;
                                                    o_daa_bits_cnt_en       <= 1'b1;                                  
                                                end
                                          else                    //IF NACK, SEND REPEATED START THEN 7E AGAIN
                                            begin
                                              state <= START;
                                            end
                                        end
                                end
                            //NO STATE TRANSITION     
                            else
                                begin
                                    state <= ACK;
                                end
                        end    
                    ENTDAA:
                        begin

                                                         o_daa_rx_mode           <= 2'b10;  // 2024 : rx must stay in arbitration mode in every single transmitting case


                        daa_mode <= 1'b1;
                        ccc_to_par <= 1'b1;                            
                          if (i_scl_daa_neg_edge && i_tx_daa_mode_done)
                            begin



                              state <= PARITY;
                              o_daa_regf_rd_en        <= 1'b1; 
                              o_daa_regf_wr_en        <= 1'b0; 
                              o_daa_regf_data_wr      <= 8'b0; 
                              o_daa_regf_addr         <=  'd49; 
                              o_daa_tx_mode           <= 3'b011; //PARITY
                              o_daa_tx_en             <= 1'b1;  
                              o_daa_bits_cnt_en       <= 1'b0;                                                            
                            end
                          else
                            begin
                              state <= ENTDAA;
                            end                             
                        end
                    PARITY:
                        begin  
                                                                         o_daa_rx_mode           <= 2'b10;  // 2024 : rx must stay in arbitration mode in every single transmitting case                                                 
                          if (i_scl_daa_neg_edge )
                            begin
                                if(ccc_to_par)
                                //PARITY AFTER ENTDAA SO NEXT STATE IS A REPEATED START
                                    begin
                                        state <= START;
                                        ccc_to_par <= 0;
                                    end
                                else
                                //PARITY AFTER ASSIGNED ADDRESS SO NEXT STATE IS ACK 
                                    begin
                                         o_daa_rx_mode           <= 2'b00;  // 2024 : wdy el RX le ACK state
                                        state <= ACK;
                                    end
                            end
                          else
                            begin
                                state <= PARITY;
                            end  
                        end
                     READ_DATA:
                        begin
                            if(i_scl_daa_neg_edge)
                                begin
                                    if (frames_count == 3'b111)
                                        begin
                                                                         o_daa_rx_mode           <= 2'b10;  // 2024 : rx must stay in arbitration mode in every single transmitting case 
                                            state <= DAA;
                                            frames_count <= 0;                         
                                            o_daa_regf_rd_en        <= 1'b1;          
                                            o_daa_regf_wr_en        <= 1'b0;  
                                            o_daa_regf_addr         <= 10'd80  ; // 2024 
                                            o_regf_wr_data_mux_sel  <= 1'b1;       
                                            o_daa_regf_data_wr      <= {first_address + addresses_count , 1'b0};                
                                            o_daa_tx_en             <= 1'b1;
                                            o_daa_bits_cnt_en       <= 1'b1;                                                                                                                       
                                        end                                    
                                    else if(i_rx_daa_mode_done)
                                        begin
                                            if (frames_count == 'd6) begin 
                                            frames_count    <= frames_count    + 1'b1;
                                            state           <= READ_DATA;                                                
                                            end 
                                            else begin 
                                            frames_count    <= frames_count    + 1'b1;
                                            state           <= READ_DATA;
                                            o_daa_regf_addr <= o_daa_regf_addr + 1'b1;
                                            end
                                        end                       
                                end
                            else 
                                begin
                                    state <= READ_DATA;
                                end                                                  
                        end 
                     DAA:
                        begin                        
                            o_daa_regf_rd_en        <= 1'b1;          
                            o_daa_regf_wr_en        <= 1'b0;                        
                            o_daa_tx_mode           <= 3'b001; //SERIALIZING ADDRESS 7 BITS
                            o_daa_tx_en             <= 1'b1;
                            o_regf_wr_data_mux_sel  <= 1'b0;  
                            if(i_scl_daa_neg_edge && i_tx_daa_done)
                                begin

                                    state <= PARITY;
                                    o_daa_regf_rd_en        <= 1'b1; 
                                    o_daa_regf_wr_en        <= 1'b0; 
                                    o_daa_regf_data_wr      <= 8'b0; 
                                    o_daa_tx_mode           <= 3'b011; //PARITY
                                    o_daa_tx_en             <= 1'b1;
                                    o_daa_bits_cnt_en       <= 1'b0;
                                end
                            else
                                begin
                                    state <= DAA;
                                end                                                   
                        end                                                                 
                     FINISH:
                        begin
                            o_daa_rx_mode           <= 2'b10;  // 2024 : rx must stay in arbitration mode in every single transmitting case
                            o_daa_mcu_done <= 1'b1;
                            if(i_scl_daa_neg_edge && i_tx_daa_mode_done)
                                begin
                                    state <= DAA_IDLE;
                                end
                            else
                                begin
                                    state <= FINISH;
                                end                                                   
                        end                                                                                                                                                                                                    
                endcase
            end   
    end    




// THE MUX IS THE REMAINING


endmodule
`default_nettype wire
//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Yaseen Salah , Nour Eldeen Samir , Mostafa Hassan
// Revision: Nour Eldeen Samir , Mostafa Hassan >>
//         -- Added reg file autput signal
//         -- removed demuxing as no need (only one bus will write in the reg file)
//         -- removed valid signal reg (delay) as it will synch with data
//
// Version : 2.0
//
// Create Date:  12:31 PM     12/21/2022
// Design Name:  Controller Rx
// Module Name:  controller_rx
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
module controller_rx(
    input   wire           i_clk                  , // system clk
    input   wire           i_rst_n                , // system reset
    input   wire           i_sdr_rx_scl           , // scl bus input from scl_generation
    input   wire           i_sdr_rx_en            , // rx block enable from sdr_controller
    input   wire           i_sdr_rx_sda           , // sda bus input from sda_handling
    input   wire  [2:0]    i_sdr_rx_des_count     , // bit count input from bits_counter
    input   wire  [2:0]    i_sdr_rx_mode          , // rx mode input 0 >> deser, 1 >> Tbit
    input   wire           i_fcnt_last_frame      , // last frame flag from frame_counter
	  input   wire           i_timer_cas            , //added by mostafa
	  input   wire           i_sdr_rx_scl_pos_edge  , //added by mostafa
    //output  reg            o_sdr_rx_valid       , // flag for ready valid parallel data
    input   wire           i_sdr_rx_tx_ser_data     ,
 	  output  reg            o_crh_start_detected    ,
    output  reg            o_sdr_rx_nack_ack      , // Ack output for the sdr_controller
    output  reg            o_sdr_rx_rd_abort      , // T_bit 0 >> abort reading , T_bit 1 >> check i_fcnt_last_frame
    output  reg   [7:0]    o_sdr_rx_regf_data_wr  , // receiver parallel data output to reg file
    output  reg            o_sdr_rx_mode_done     , // rx block done flag
    output  reg            o_sdr_rx_pp_mode_done,
    //output  reg            last_bit_flag  ,
    output  wire           o_sdr_rx_arbitration_lost
    );



reg [7:0] arbitrated_adress ;

reg sdr_rx_arbitration_lost ;
assign o_sdr_rx_arbitration_lost = sdr_rx_arbitration_lost ;

//-- i_ser_mode parameters --------------------------------------------------

localparam ACK             = 3'b000 ; // 0
localparam DESERIALIZING   = 3'b001 ; // 1
localparam T_BIT           = 3'b011 ; // 3
localparam ARBITRATION     = 3'b010 ; // 2
localparam CHECK_FOR_START = 3'b110 ; // 6


//-- reciever --------------------------------------------------

always @(posedge i_clk or negedge i_rst_n)
  begin : proc_deserializer
    if(!i_rst_n)
      begin
        o_sdr_rx_nack_ack            <=  1'b1 ;
        o_sdr_rx_rd_abort            <=  1'b0 ;
        o_sdr_rx_mode_done           <=  1'b0 ;
        o_sdr_rx_pp_mode_done <= 1'b0 ;
        o_sdr_rx_regf_data_wr        <=  8'b0 ;
        sdr_rx_arbitration_lost   <=  1'b0 ;
        arbitrated_adress <='b0;

      end
    else if (i_sdr_rx_en)
      begin
        o_sdr_rx_mode_done <=  1'b0 ;
        o_sdr_rx_pp_mode_done <= 1'b0 ;
        case (i_sdr_rx_mode)
          ACK           : begin // NEED TO BE REDONE

                            o_sdr_rx_mode_done <=  1'b0 ;
                            o_sdr_rx_pp_mode_done <= 1'b0 ;
                            sdr_rx_arbitration_lost <=1'b0;
                            // missing 
                            if (i_sdr_rx_scl)
                              begin
                                o_sdr_rx_nack_ack  <= i_sdr_rx_sda ; // 1sda >> nack , 0sda >> ack
                                o_sdr_rx_mode_done <= 1'b1         ;
                              end
                          end

          DESERIALIZING : begin
                            o_sdr_rx_mode_done <=  1'b0 ;
                            o_sdr_rx_pp_mode_done <= 1'b0 ;
                            //last_bit_flag      <=  1'b0 ;
                            sdr_rx_arbitration_lost <=1'b0;

                            if (i_sdr_rx_scl)
                              begin
                                o_sdr_rx_regf_data_wr[i_sdr_rx_des_count] <= i_sdr_rx_sda ;
                              end
                            /*if(&i_sdr_rx_des_count && )
                              begin
                                last_bit_flag <= 1'b1 ;
                              end */

                            if (!i_sdr_rx_des_count && i_sdr_rx_scl_pos_edge )
                              begin
                                //last_bit_flag <= 1'b1 ;
                                o_sdr_rx_pp_mode_done <=  1'b1 ;
                              end

                            if (!i_sdr_rx_des_count )
                              begin
                                o_sdr_rx_mode_done <=  1'b1 ;
                              end

                          end

                    T_BIT : begin

                            o_sdr_rx_mode_done <=  1'b0 ;
                            o_sdr_rx_pp_mode_done <= 1'b0 ;
                            sdr_rx_arbitration_lost <=1'b0;

                            if (i_sdr_rx_scl)
                              begin
                                if (!i_sdr_rx_sda)
                                  begin
                                    o_sdr_rx_rd_abort  <=  1'b1 ;
                                    o_sdr_rx_mode_done <=  1'b1 ;
                                  end
                                else
                                  begin
                                    if (i_fcnt_last_frame)
                                      begin
                                        o_sdr_rx_rd_abort  <=  1'b1 ;
                                        o_sdr_rx_mode_done <=  1'b1 ;
                                      end
                                    else
                                      begin
                                        o_sdr_rx_rd_abort  <=  1'b0 ;
                                        o_sdr_rx_mode_done <=  1'b1 ;
                                      end
                                  end
                              end
                          end

              CHECK_FOR_START : begin                                
                            o_sdr_rx_mode_done <=  1'b0 ;
                            o_sdr_rx_pp_mode_done <= 1'b0 ;
                            if (!i_timer_cas)
                              begin
                                if(!i_sdr_rx_scl) //added by mostafa
								                  begin
                                    if (!i_sdr_rx_sda)
                                      begin
 								                        o_crh_start_detected <= 1'b1 ; //added by mostafa
                                        o_sdr_rx_mode_done <=  1'b1 ;
                                      end
                                    else
                                      begin
									                      o_crh_start_detected <= 1'b0 ; //added by mostafa
									                      o_sdr_rx_mode_done <=  1'b1 ;
                                        if (i_fcnt_last_frame)
                                          begin
                                            o_sdr_rx_rd_abort  <=  1'b1 ;
                                            //o_sdr_rx_mode_done <=  1'b1 ;
                                          end
                                        else
                                          begin
                                            o_sdr_rx_rd_abort  <=  1'b0 ;
                                            //o_sdr_rx_mode_done <=  1'b1 ;
                                          end
                                      end
                                  end
                                end
								               else //added by mostafa
								                 begin
								                   o_sdr_rx_mode_done <=  1'b0 ;
								                 end
                          end

            ARBITRATION    : begin           // 2024 note : should be treated as idle state 

                                if ( i_sdr_rx_scl && !sdr_rx_arbitration_lost)
                                   begin
                                      sdr_rx_arbitration_lost <= i_sdr_rx_tx_ser_data^i_sdr_rx_sda;  // 1 if they arent the same
                                      arbitrated_adress [i_sdr_rx_des_count-1] <= i_sdr_rx_sda ;
                                    end
                                 else if ( (i_sdr_rx_des_count=='b0) && sdr_rx_arbitration_lost)
                                    begin
                                      o_sdr_rx_regf_data_wr <= arbitrated_adress ;
                                      o_sdr_rx_mode_done <=  1'b1 ;
                                   end
                                else if (i_sdr_rx_scl)
                                   begin
                                      arbitrated_adress [i_sdr_rx_des_count-1] <= i_sdr_rx_sda ;
                                    end
                             end
        endcase
      end
    else
      begin
        o_sdr_rx_rd_abort <= 1'b0 ;
        sdr_rx_arbitration_lost <= 1'b0 ;
        o_sdr_rx_mode_done <=  1'b0 ;
        o_sdr_rx_pp_mode_done <=  1'b0 ;
      end
  end

endmodule
`default_nettype wire

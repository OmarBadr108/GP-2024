//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//

// Revision: Nour Eldeen Samir , Yaseen Salah
//
// Version : 2.0
//

// Design Name:  Controller Tx
// Module Name:  controller_tx
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
module controller_tx (
    input   wire           i_clk               ,
    input   wire           i_rst_n             ,
    input   wire           i_ser_scl           ,
    input   wire           i_ser_scl_neg_edge  ,
    input   wire           i_ser_scl_pos_edge  ,
    input   wire           i_ser_en            , // to enable the serializer as long as we're in TX
    input   wire           i_ser_valid         , // to load a new frame "must be a pulse" //UNUSED
    input   wire  [2:0]    i_ser_count         ,
    input   wire           i_ser_count_done    ,
    input   wire  [2:0]    i_ser_mode          ,
    input   wire  [7:0]    i_ser_regf_data     ,
    input   wire           i_timer_cas         , // input from timer block for start condition
    output  reg            o_ser_sda_low       ,//added by mostafa 
    output  reg            o_stop_pattern      , // output to i3c_timer block
    output  reg            o_start_pattern     , // output to i3c_timer block
    output  reg            o_ser_s_data        ,
    output  reg            o_ser_mode_done     ,
    output  reg            o_ser_pp_mode_done  , //early mode_done for push_pull short periods
    output  reg            o_tx_daa_done       ,
    output  reg            o_ser_to_parity_transition

    );


  //-- i_ser_mode parameters --------------------------------------------------


    localparam START_BIT      = 3'b000 ;
    localparam SERIALIZING    = 3'b001 ;
    localparam PARITY         = 3'b011 ;
    localparam STOP           = 3'b010 ;
    localparam CTRL_ACK       = 3'b111 ;  //  To be changed from 3'b100 to 3'b111 in HJ and I2C
    localparam Hold_Zero      = 3'b100 ;
    localparam CTRL_NACK      = 3'b101 ;
    localparam REPEATED_START = 3'b110 ;
    //localparam EXIT_PATTERN   = 3'b ;



  //-- internal wires declaration ---------------------------------------------
reg last_bit_flag ;

  //-- transmitter ------------------------------------------------

    always @(posedge i_clk or negedge i_rst_n)
      begin : proc_serializer


        if(~i_rst_n)
          begin
            o_ser_mode_done    <= 1'b0 ;
            o_ser_pp_mode_done <= 1'b0 ;
            o_ser_s_data  <=  1'b1 ;
            o_ser_to_parity_transition <= 1'b0 ;
            o_ser_sda_low <= 1'b0 ;
            last_bit_flag <= 1'b0 ;

            o_tx_daa_done <= 1'b0;
           // temp            <=  ser_p_mux_out;
          end

        else if (i_ser_en)
          begin
            case (i_ser_mode)
              START_BIT   : begin
                              o_start_pattern <= 1'b0 ; 
                              o_stop_pattern  <= 1'b0 ;
                              o_ser_mode_done <= 1'b0 ;
                              o_ser_to_parity_transition <= 1'b0;
                              o_ser_s_data    <= 1'b1 ; // need to check if it will make problems to anyone
                              o_ser_sda_low <= 1'b0 ;
                              if (i_ser_scl)
                                begin
                                  o_ser_s_data    <= 1'b0 ;
                                  o_start_pattern <= 1'b1 ;

                                  if (i_timer_cas)
                                    begin
                                      o_start_pattern <= 1'b0 ;
                                      o_ser_mode_done <= 1'b1 ;
                                    end
                                  else
                                    begin
                                      o_start_pattern <= 1'b1 ;
                                      o_ser_mode_done <= 1'b0 ;
                                    end

                                end
                            end
              SERIALIZING : begin
                            o_ser_mode_done <= 1'b0;
                            o_ser_to_parity_transition <= 1'b1;
                            o_ser_sda_low <= 1'b0 ;
                              if(i_ser_count_done)
                                begin
                                    o_ser_mode_done <= 1'b1;
                                end
                              else
                                begin
                                    o_ser_mode_done <= 1'b0;
                                end

                                //for push-pull
                                if (i_ser_scl_pos_edge && !i_ser_count)
                                  begin
                                    o_ser_pp_mode_done <= 1'b1 ;
                                  end
                                else
                                  begin
                                    o_ser_pp_mode_done <= 1'b0 ;
                                  end

                              if (!i_ser_scl)
                                begin
                                  o_ser_s_data    <= i_ser_regf_data[i_ser_count] ;
                                end

                               if(i_ser_count == 3'b1)
                                    begin
                                        o_tx_daa_done <= 1'b1;
                                    end
                                  else
                                    begin
                                        o_tx_daa_done <= 1'b0;
                                    end
                          end

              PARITY      : begin
                              o_ser_mode_done    <= 1'b0 ;
                              o_ser_pp_mode_done <= 1'b0 ;
                              o_ser_to_parity_transition <= 1'b0;
                              o_ser_sda_low <= 1'b0 ;
                             if (i_ser_count_done)
                                o_ser_mode_done <= 1'b1;
                              else
                                o_ser_mode_done <= 1'b0;
                                 //unused-wrong implementation
                              if (!i_ser_scl)
                                begin
                                  o_ser_s_data    <= ~^i_ser_regf_data ;
                                  //o_ser_mode_done    <= 1'b1 ;
                                end

                              //for push-pull
                              if (i_ser_scl_pos_edge)
                                begin
                                  o_ser_pp_mode_done <= 1'b1 ;
                                end
                            end

              STOP        : begin
                              o_ser_s_data    <= 1'b0 ;
                              o_ser_mode_done <= 1'b0;
                              o_ser_to_parity_transition <= 1'b0;
                              o_ser_sda_low <= 1'b0 ;
                              if (i_ser_scl)
                                begin
                                  o_stop_pattern  <= 1'b1 ;
                                  o_ser_s_data    <= 1'b1 ;
                                  o_ser_mode_done <= 1'b1 ;
                                end
                            end
              CTRL_ACK    : begin
                              o_start_pattern <= 1'b0 ;
                              o_ser_s_data <= 1'b0 ;
                              o_ser_sda_low <= 1'b1 ; //added by mostafa
                              o_ser_mode_done <= 1'b0;
                              o_ser_to_parity_transition <= 1'b0;
                            if (i_ser_scl_pos_edge)
                                begin
                                  //o_ser_s_data    <= 1'b1 ;
                                  o_ser_mode_done <= 1'b1 ;
                                  o_ser_sda_low <= 1'b0 ; //added by mostafa
                                  o_start_pattern <= 1'b1 ;
                                end
                            
                            
                            
                                

                                
                                
                                
                                
                              /*if (i_ser_scl)
                                begin
                                  o_start_pattern <= 1'b1 ;
                                end */
                                
                                
                                
                            end


                CTRL_NACK  : begin
                              o_ser_sda_low <= 1'b0 ;
                              o_ser_s_data <= 1'b1 ;
                              o_ser_mode_done <= 1'b0;
                              o_ser_to_parity_transition <= 1'b0;

                            if (i_ser_scl_pos_edge)
                                begin
                                  o_ser_mode_done <= 1'b1 ;
                                end
                           end

              REPEATED_START : begin
                              o_ser_sda_low <= 1'b0 ;
                              o_ser_mode_done <= 1'b0 ;
                              o_ser_to_parity_transition <= 1'b0;
                              if (!i_ser_scl)
                                begin
                                  o_ser_s_data    <= 1'b1 ;
                                end
                              else
                                begin
                                  o_ser_s_data    <= 1'b0 ;
                                end

                              if (i_ser_scl_pos_edge)
                                begin
                                  o_ser_mode_done <= 1'b1 ;
                                end
                            end

              Hold_Zero    : begin
                              o_ser_s_data    <= 1'b0 ;
                             end
                             
                             
              EXIT_PATTERN : begin
                             end
              
            endcase
          end
        else
            begin
                o_ser_sda_low <= 1'b0 ;
                o_ser_s_data       <= 1'b1 ;
                o_ser_mode_done    <= 1'b0 ;
                o_ser_pp_mode_done <= 1'b0 ;
                last_bit_flag      <= 1'b0 ;
            end
      end

endmodule
`default_nettype wire


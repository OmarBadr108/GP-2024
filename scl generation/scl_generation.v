//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Zyad Sobhi , Youssef Essam, Youssef Amr
// Revision: Yaseen Salah
//
// Version : 1.0
//
// Create Date:  6:32 AM     12/18/2022
// Design Name:  scl_generation
// Module Name:  scl_generation
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
module scl_generation(
    input  wire       i_sdr_ctrl_clk          ,   // 50 MHz clock
    input  wire       i_sdr_ctrl_rst_n        ,
    input  wire       i_sdr_scl_gen_pp_od     ,   // 1: Push-Pull      // 0: for Open-Drain
    input  wire       i_scl_gen_stall         ,  // 1 for stalling
    input  wire       i_sdr_ctrl_scl_idle     ,
    input  wire       i_timer_cas             ,
    output reg        o_scl_pos_edge          ,
    output reg        o_scl_neg_edge          ,
    output reg        o_scl                  );


//-- states encoding in gray ---------------------------------------------

localparam LOW  = 1'b0 ;
localparam HIGH = 1'b1 ;


//-- internal wires declaration -------------------------------------------

reg          state   ;  //assigned at fsm
reg  [6:0]   count   ;  //assigned at counter
reg          switch  ;  //assigned at counter


//-- scl generation fsm ---------------------------------------------------

always @(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
  begin: scl_generation_fsm

    if (!i_sdr_ctrl_rst_n)
      begin
        //-- state
          state   <=  HIGH   ;
        //-- outputs
          o_scl   <=  1'b1  ;
          o_scl_pos_edge <= 1'b0;
          o_scl_neg_edge <= 1'b0;
      end

    else
      begin
        case (state)
          LOW: begin
                o_scl_neg_edge <= 1'b0;
                if (i_scl_gen_stall) begin
                 state <=   LOW  ;
                end
                else begin
                    if (switch)
                      begin
                        o_scl <=   1'b1 ;
                        state <=   HIGH ;
                        o_scl_pos_edge <= 1'b1;
                      end
                    else
                      begin
                        o_scl <=   1'b0 ;
                        state <=   LOW  ;
                        o_scl_pos_edge <= 1'b0;
                      end
                end
            end

          HIGH:
            begin
            o_scl_pos_edge <= 1'b0;
                if (i_scl_gen_stall) begin
                  state <=   LOW  ;
                end
                else if ((switch && !i_sdr_ctrl_scl_idle) || (i_timer_cas) )
                  begin
                    o_scl <=   1'b0 ;
                    state <=   LOW  ;
                    o_scl_neg_edge <= 1'b1;
                  end
                else
                  begin
                    o_scl <=   1'b1 ;
                    state <=   HIGH ;
                    o_scl_neg_edge <= 1'b0;
                  end
            end
        endcase
      end
  end
//-- switch generation counter --------------------------------------------

always @(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
  begin: scl_generation_counter

    if (!i_sdr_ctrl_rst_n)
      begin
          count  <= 7'b1 ;
          switch <= 1'b0 ;
      end

  // 50 MHz/4 = 12.5 MHz for Push-Pull
    else if (i_sdr_scl_gen_pp_od)
      begin
          if (count >= 7'd2)
            begin
              count  <= 7'b1 ;
              switch <= 1'b1 ;
            end
          else
            begin
              count  <= count + 1'b1 ;
              switch <= 1'b0 ;
            end
      end

  // 50 MHz/125 = 400 KHz for Open-Drain
    else
      begin
          if (count == 7'd62)
            begin
              switch <= 1'b1;
              count <= count + 1'b1;
            end
          else if (count == 7'd125)
            begin
              count  <= 7'b1 ;
              switch <= 1'b1;
            end
          else
            begin
              count <= count + 1'b1;
              switch <= 1'b0;
            end
      end

  end



endmodule
`default_nettype wire

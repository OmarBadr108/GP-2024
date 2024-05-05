//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Nour Eldeen Samir  
// Revision: 
//
// Version : 2.0
//
// Create Date:  12:45 AM     03/07/2023 
// Design Name:  i3c_timer_fsm
// Module Name:  i3c_timer_fsm
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

module i3c_timer_fsm (
                      input  wire          i_clk                      , // system clock 50MHZ from FPGA
                      input  wire          i_rst_n                    , // asynch active low reset 
                      input  wire          i_start_pattern            , // start pattern flag input from tx
                      input  wire          i_stop_pattern             , // stop pattern flag input from tx
                      input  wire          i_chr_set                  , // input from crh of activity state set
                      input  wire  [1:0]   i_crh_entasx               , // enter activity states input value
                      input  wire          i_i3c_idle_flag            , // stop is done and od 
                      output reg           o_timer_cas                , // clock after start flag 
                      output reg           o_timer_bus_free_pure      , // pure i3c bus condition >> after tcas 
                      output reg           o_timer_bus_free_mix_fm    , // clock for bus free condition when fm
                      output reg           o_timer_bus_free_mix_fm_p  , // clock for bus free condition when fm+
                      output reg           o_timer_bus_aval           , // clock for available bus condition 
                      output reg           o_timer_bus_idle           , // clock for idle bus condition 
                      output reg           o_timer_crhpol             , // clock for new controller handoff
                      output reg           o_timer_newcrlck_i2c       , // clock for new controller driving SDA when i2c
                      output reg           o_timer_newcrlck_i3c      ); // clock for new controller driving SDA when i3c
 
//`include "timings.v"


// system clock is 50 MHZ >> period is 20 ns 
// T_ENTAS3 is default when no target supports ENTASx CCC

// -- Start and Stop timings 
localparam T_CAS            = 24'd2       ; // 38.4 ns ~ 40 ns //garanteed
//localparam T_CBP            = 24'd1       ; // 19.2 ns ~ 20 ns //garanteed 

// -- Bus Condition timings
// T_AVAL = T_ENTAS0 = T_NEWCRLOCK_I3C = 1 us
localparam T_BUF_FM         = 24'd25      ; // 0.5 us = 500 ns >> 500/20 = 25 cycles 
localparam T_BUF_FM_P       = 24'd65      ; // 1.3 us = 1300 ns >> 1300/20 = 65 cycles 
localparam T_AVAL           = 24'd50      ; // 1 us = 1000 ns >> 1000/20 = 50 cycles
localparam T_IDLE           = 24'd10000   ; // 200 us = 200000 ns >> 200000/20 = 10000

// -- Activity States timings
localparam T_ENTAS1         = 24'd5000    ; // 100 us = 100000 ns >> 100000/20 = 5000 cycles
localparam T_ENTAS2         = 24'd100000  ; // 2 ms = 2000000 ns >> 2000000/20 = 100000 cycles
localparam T_ENTAS3         = 24'd2500000 ; // 50 ms = 50000000 ns >> 50000000/20 = 2500000 cycles 

// -- Control Role Handoff timings
localparam T_CRHPOverlap    = 24'd11      ; // (200 + 12 = 212 ns ~ 200 + 10 = 210 ns) >> 21/2 cycles 
localparam T_NEWCRLOCK_I2C  = 24'd15      ; // 300 ns >> 300/20 = 15 cycles





localparam ENTER_ACTIVITY_STATE_0  = 2'b00 ;
localparam ENTER_ACTIVITY_STATE_1  = 2'b01 ;
localparam ENTER_ACTIVITY_STATE_2  = 2'b10 ;
localparam ENTER_ACTIVITY_STATE_3  = 2'b11 ;

localparam IDLE                    = 3'b100;
localparam POST_STOP_CALCULATIONS  = 3'b101;
localparam POST_START_CALCULATIONS = 3'b111;


// timer_states <<<<

// TBD after this block is done >>
// wire i_i3c_idle_flag  ;
// assign i_i3c_idle_flag = i_dda_idle_flag | i_sdr_idle_flag | i_crh_idle_flag;

reg  [2:0]   timer_state            ;
reg          idle_flag_pulse        ;
reg  [23:0]  count                  ;
reg  [23:0]  stp_to_idle_trans_time ;

always @(posedge i_clk or negedge i_rst_n) 
  begin: i3c_timings_counter
    if (!i_rst_n) 
      begin  
        o_timer_cas                <= 1'b0 ;     
        o_timer_bus_free_pure      <= 1'b0 ; 
        o_timer_bus_free_mix_fm    <= 1'b0 ; 
        o_timer_bus_free_mix_fm_p  <= 1'b0 ; 
        o_timer_bus_aval           <= 1'b0 ; 
        o_timer_bus_idle           <= 1'b0 ; 
        o_timer_crhpol             <= 1'b0 ; 
        o_timer_newcrlck_i2c       <= 1'b0 ;
        o_timer_newcrlck_i3c       <= 1'b0 ;
        idle_flag_pulse            <= 1'b0 ;
        count                      <= 24'b0;
        stp_to_idle_trans_time     <= 24'b0;

      end 
    else 
      begin

        case (timer_state)

          IDLE: 
            begin 
              o_timer_cas                <= 1'b0 ;    
              idle_flag_pulse            <= 1'b0 ;
              count                      <= 24'b0;
              stp_to_idle_trans_time     <= 24'b0;

                if (i_stop_pattern)
                  begin 
                    count       <= count + 1'b1 ;
                    timer_state <= POST_STOP_CALCULATIONS;
                  end

                else if (i_start_pattern)
                  begin
                    count                      <= count + 1'b1 ;
                    timer_state                <= POST_START_CALCULATIONS;
                    o_timer_bus_idle           <= 1'b0 ;
                    o_timer_bus_free_pure      <= 1'b0 ; 
                    o_timer_bus_free_mix_fm    <= 1'b0 ; 
                    o_timer_bus_free_mix_fm_p  <= 1'b0 ; 
                    o_timer_bus_aval           <= 1'b0 ;  
                    o_timer_crhpol             <= 1'b0 ; 
                    o_timer_newcrlck_i2c       <= 1'b0 ;
                    o_timer_newcrlck_i3c       <= 1'b0 ;
                  end 

            end

          POST_STOP_CALCULATIONS:
            begin 
              count  <= count + 1'b1  ;

            //---- bus conditions and controller overlap time  
              if (count == T_CAS)
                begin: bus_free_pure_condition                 // bus has become in free condition 
                  o_timer_bus_free_pure     <= 1'b1 ;         //  for any pure I3C device who may concern
                  
                end   

              else if (count == T_CRHPOverlap)                 // bus is ready for new controller handoff
                begin: control_role_handoff_overlap    
                  o_timer_crhpol            <= 1'b1 ;   
                end  

              else if (count == T_BUF_FM)                      // bus has enetered free condition 
                begin: bus_free_mixed_condition_fmode         //  for fast mode I2C devices who may concern
                  o_timer_bus_free_mix_fm   <= 1'b1 ;   
                end 

              else if (count == T_AVAL)                        // bus has enetered available condition 
                begin: bus_available_condition                //  IBI is free to take place 
                  o_timer_bus_aval          <= 1'b1 ;
                end

              else if (count == T_BUF_FM_P)                    // bus has enetered free condition 
                begin: bus_free_mixed_condition_fmode_plus    //  for fast mode plus I2C devices who may concern
                  o_timer_bus_free_mix_fm_p <= 1'b1 ;
                end

              else if (count == T_IDLE)                        // bus has enetered idle condition
                begin: bus_idle_condition                     //  Hot-Join is free to take place 
                  o_timer_bus_idle          <= 1'b1 ;
                  timer_state               <= IDLE ;
                end

              else 
                begin
                  timer_state  <= POST_STOP_CALCULATIONS ;
                  count        <= count + 1'b1           ;
                end

            //---- transition from stop to idle (assumed od) 
              if (i_i3c_idle_flag) 
                begin: capturing_count_and_wait_till_NEWCRLOCK

                  idle_flag_pulse <= 1'b1 ;

                    if (i_i3c_idle_flag && !idle_flag_pulse) 
                      begin:capturing_transition_time
                        stp_to_idle_trans_time <= count ;
                    end  
                end
              else 
                begin 
                  idle_flag_pulse <= 1'b0 ;
                end

              if (count == stp_to_idle_trans_time + T_NEWCRLOCK_I2C)
                begin: new_ctrl_lock_i2c
                  o_timer_newcrlck_i2c    <= 1'b1 ;
                end                      
              else if (count == stp_to_idle_trans_time + T_AVAL)
                begin: new_ctrl_lock_i3c
                  o_timer_newcrlck_i3c    <= 1'b1 ;
                end

            end
         

          POST_START_CALCULATIONS:
            begin 
              count  <= count + 1'b1  ;

              if (!i_chr_set) 
                begin: no_activity_states_needed 
                
                      o_timer_cas  <= 1'b1  ;
                      timer_state  <= IDLE  ;         

                end 
              else 
                begin 

                  case (i_crh_entasx)

                    ENTER_ACTIVITY_STATE_0: 
                      begin 

                        if (count == T_AVAL)
                          begin 
                            o_timer_cas  <= 1'b1  ;
                            timer_state  <= IDLE  ;
                          end 
                        else
                          begin
                            o_timer_cas  <= 1'b0  ;
                            timer_state  <= POST_START_CALCULATIONS ;
                          end        
                      end 
                    ENTER_ACTIVITY_STATE_1:
                      begin 

                        if (count == T_ENTAS1)
                          begin 
                            o_timer_cas  <= 1'b1  ;
                            timer_state  <= IDLE  ;
                          end 
                        else
                          begin
                            o_timer_cas  <= 1'b0  ;
                            timer_state  <= POST_START_CALCULATIONS ;
                          end    

                      end 
                    ENTER_ACTIVITY_STATE_2:
                      begin 

                        if (count == T_ENTAS2)
                          begin 
                            o_timer_cas  <= 1'b1  ;
                            timer_state  <= IDLE  ;
                          end 
                        else
                          begin
                            o_timer_cas  <= 1'b0  ;
                            timer_state  <= POST_START_CALCULATIONS ;
                          end        

                      end 
                    ENTER_ACTIVITY_STATE_3:
                      begin 

                        if (count == T_ENTAS3)
                          begin 
                            o_timer_cas  <= 1'b1  ;
                            timer_state  <= IDLE  ;
                          end 
                        else
                          begin
                            o_timer_cas  <= 1'b0  ;
                            timer_state  <= POST_START_CALCULATIONS ;
                          end        

                      end 
                  endcase
                end 
            end

          default: 
                 timer_state  <= IDLE ;
      endcase  
  end 
end 

endmodule

`default_nettype wire           








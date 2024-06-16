//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Mostafa Hassan   
// Revision:  
//         
//
// Version : 2.0
//
// Create Date:  02:31 AM     02/27/2023 
// Design Name:  controller_role_handoff_target
// Module Name:  controller_role_handoff_target
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
module controller_crh (
//inputs from system top  
input  wire              i_crh_clk,
input  wire              i_crh_rst_n,
//inputs from i3c_engine
input  wire              i_crh_en,
input  wire              i_crh_initiated_request,
input  wire              i_crh_stop_is_sent,
//inputs from reg file
input  wire  [7:0]       i_crh_CRHDLY,
input  wire  [7:0]       i_crh_getstatus_data,
input  wire  [7:0]       i_crh_CRCAP2,
input  wire  [7:0]       i_crh_PRECR,
input  wire  [7:0]       i_crh_cfg_reg,
input  wire  [7:0]       i_crh_tgts_count,
//inputs from controller tx
input  wire              i_crh_tx_mode_done,
input  wire              i_crh_tx_pp_mode_done,
input  wire              i_crh_sda_low,
//inputs from controller rx
input  wire              i_crh_rx_mode_done,
input  wire              i_crh_rx_pp_mode_done,
input  wire              i_crh_rx_nack_ack, //if>>0 then ack, if>>1 then nack --from RX
input  wire              i_crh_scl_neg_edge,
input  wire              i_crh_scl_pos_edge,
input  wire              i_crh_start_detected,
//inputs from timer 
input  wire              i_crh_crhpoverlap,
input  wire              i_crh_newcrlock,
input  wire              i_crh_timer_cas,
//outputs to controller tx
output  reg              o_crh_tx_en, //TX enable 
output  reg  [2:0]       o_crh_tx_mode, //define the mode of TX
//outputs to controller rx
output  reg              o_crh_rx_en,
output  reg  [2:0]       o_crh_rx_mode,
//outputs to reg file
output  reg              o_crh_regf_wr_en,
output  reg              o_crh_regf_rd_en, //to be edited to pulse
output  reg  [11:0]       o_crh_regf_addr,
//outputs to i3c_engine
output  reg              o_crh_done,
//output  reg              o_crh_ncr_win,
//output  reg              o_crh_ncr_take_control,
output  reg              o_crh_send_stop,
//outputs to bits counter
output  reg              o_crh_pp_od,
output  reg              o_crh_cnt_en,
output  reg              o_crh_rx_cnt_en,
//outputs to timer
output  reg              o_crh_timer_set,
output  reg  [1:0]       o_crh_timer_entasx,
//outputs to frame counter
output  reg              o_crh_fcnt_en,
//outputs to scl generation
output  reg              o_crh_scl_idle
);


reg [3:0] state ;
reg [3:0] int_state ;

reg       REP_START_COUNT ;
reg [1:0] ACK_COUNT ;
reg [5:0] PAR_BIT_COUNT ;
reg [5:0] DATA_SENT_COUNT ;
reg [5:0] counter ;
reg       preparing_done ;
reg       stop_is_sent ;
reg       dont_repeat ;




// parameters and defines in RegFile
localparam BROADCAST_ADDR_REG_FILE = 9'd46 ; //broadcast address in reg file (7E+w)
localparam ARBITRATION_ADDR_REG_FILE = 10'd48 ; //arbitration address 
localparam TARGET_ADDR_REG_FILE =  9'd0   ; 
localparam GETSTATUS_ADDR_REG_FILE = 9'd387 ; 
localparam GETMXDS_ADDR_REG_FILE = 9'd381    ; 
localparam GETCAPS_ADDR_REG_FILE = 9'd384    ; 
localparam DISEC_ADDR_REG_FILE = 9'd104    ; 
localparam ENTAS0_ADDR_REG_FILE = 9'd393    ;
localparam ENTAS1_ADDR_REG_FILE = 9'd394    ;
localparam ENTAS2_ADDR_REG_FILE = 9'd395    ;
localparam ENTAS3_ADDR_REG_FILE = 9'd396    ;
localparam DEFTGTS_ADDR_REG_FILE = 9'd397   ;
localparam GETACCCR_ADDR_REG_FILE  = 9'd389    ;
localparam DEF_BYTE_REG_FILE = 9'd382    ;
localparam CRCAPS1_ADDR_REG_FILE = 9'd385    ;
localparam CRHDLY1_ADDR_REG_FILE = 9'd383    ;
localparam GETSTATUS_LSB_ADDR_REG_FILE = 9'd390    ;
localparam CRCAPS2_ADDR_REG_FILE  = 9'd386    ;
localparam PRECR_ADDR_REG_FILE = 9'd388 ; 
localparam GETSTATUS_MSB_ADDR_REG_FILE = 9'd408 ;
localparam DISEC_DATA_ADDR_REG_FILE  =  9'd406   ;


//internal states
localparam GETSTATUS         = 4'b0000 ;
localparam DISEC             = 4'b0001 ;
localparam ENTASx            = 4'b0011 ;
localparam GETCAPS           = 4'b0010 ;
localparam DEFTGTS           = 4'b0110 ;
localparam DEFGRPA           = 4'b0111 ;
localparam GETMXDS           = 4'b0101 ;
localparam DEFTGT            = 4'b0100 ;
localparam GETACCCR          = 4'b1100 ;
localparam GETSTATUS_DEF     = 4'b1101 ;

//global states
localparam IDLE              = 4'b0000 ;
localparam REP_START         = 4'b0001 ;
localparam ADDRESS           = 4'b0011 ; //address sent by active cr
localparam ACK               = 4'b0010 ; //ack to controller
localparam ACK_TO_SEC_CR     = 4'b0110 ; //ack to sec controller
localparam NACK_TO_SEC_CR    = 4'b0111 ; //nack to sec controller
localparam BROADCAST_ADDR    = 4'b0101 ;
localparam CCC_CODE          = 4'b0100 ; 
localparam DEF_BYTE          = 4'b1100 ;
localparam PAR_BIT           = 4'b1101 ;
localparam DATA_RETURNED_1   = 4'b1111 ;
localparam DATA_RETURNED_2   = 4'b1110 ;
localparam DATA_SENT_1       = 4'b1010 ;
localparam HANDOFF           = 4'b1011 ;
localparam TESTING           = 4'b1001 ;
localparam MONITOR           = 4'b1000 ;

always@(posedge i_crh_clk or negedge i_crh_rst_n)
begin 
  if(!i_crh_rst_n)
    begin
      state                   <= IDLE ;
      o_crh_tx_en             <= 1'b0      ;
      o_crh_tx_mode           <= 3'b0      ;
      o_crh_rx_en             <= 1'b0      ;
      o_crh_rx_cnt_en         <= 1'b0      ;
      o_crh_rx_mode           <= 2'b0      ;
      o_crh_cnt_en            <= 1'b0      ; 
      o_crh_fcnt_en           <= 1'b0      ;
      o_crh_pp_od             <= 1'b1      ;
      o_crh_done              <= 1'b0      ;
      o_crh_regf_rd_en        <= 1'b0      ;
      o_crh_regf_wr_en        <= 1'b0      ;  // write enable output  reg to reg file 
      o_crh_regf_addr         <= 9'b000000 ;
      o_crh_scl_idle          <= 1'b0      ;
      o_crh_timer_set         <= 1'b0      ;
      o_crh_timer_entasx      <= 2'b00     ;
      REP_START_COUNT         <= 1'd0      ;
      ACK_COUNT               <= 2'd0      ;
      PAR_BIT_COUNT           <= 6'd0      ;
      DATA_SENT_COUNT         <= 6'd0      ;
      counter                 <= 6'd1      ;
      dont_repeat             <= 1'b0      ;
    end
  else 
    begin 
      case(state)
        IDLE : begin
          o_crh_scl_idle          <= 1'b0      ;
          o_crh_pp_od             <= 1'b0      ;
          o_crh_timer_set         <= 1'b0      ;
          o_crh_timer_entasx      <= 2'b00     ;
          o_crh_regf_rd_en        <= 1'b1      ;
          o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;
           dont_repeat             <= 1'b0      ;
          if(i_crh_en && !dont_repeat)
            begin
              if(i_crh_initiated_request) //initiated by active controller
                begin
                  o_crh_tx_en             <= 1'b1      ;
                  o_crh_tx_mode           <= 3'b110    ;
                  o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                  o_crh_scl_idle          <= 1'b0      ;
                  state                   <= REP_START ;
                  int_state               <= GETSTATUS ;   
                end

              else   //controller role request condition
                begin
                  if(i_crh_cfg_reg[0]) // controller ack 
                    begin
                      o_crh_tx_en             <= 1'b1      ;
                      o_crh_tx_mode           <= 3'b111    ; //ack in tx
                      o_crh_pp_od             <= 1'b1      ;
                      state                   <= ACK_TO_SEC_CR ;
                    end
                  else
                    begin
                      o_crh_tx_en             <= 1'b1      ;
                      o_crh_tx_mode           <= 3'b101    ; //nack(high-z) in tx
                      o_crh_pp_od             <= 1'b1      ;
                      state                   <= NACK_TO_SEC_CR ;
                    end
                end 
             end  
          else
            begin
              state <= IDLE ; 
            end 
                 
            
        end 
        
        ACK_TO_SEC_CR : begin //ack to the sec cr
        o_crh_pp_od             <= 1'b1      ; //rep start is push pull
        if(i_crh_tx_mode_done )
          begin
            o_crh_rx_en             <= 1'b0      ;
            o_crh_tx_en             <= 1'b1      ;
            o_crh_tx_mode           <= 3'b110    ;
            o_crh_pp_od             <= 1'b1      ; //rep start is push pull
            state <= REP_START ;
            int_state <= GETCAPS ;
          end
        else
          begin
            state <= ACK_TO_SEC_CR ;
          end 
        
          
          end 
          
          
        NACK_TO_SEC_CR : begin //nack to the sec cr
        o_crh_pp_od             <= 1'b1      ; 
        if(i_crh_tx_mode_done )
          begin
            o_crh_pp_od             <= 1'b0      ; 
            state <= IDLE ;
            o_crh_scl_idle          <= 1'b1      ;
            o_crh_done              <= 1'b1      ;
          end
        else
          begin
            state <= NACK_TO_SEC_CR ;
          end 
        

          end 
          
        REP_START : begin
         
          if(i_crh_tx_mode_done  )
            begin
              case(int_state)
                  GETSTATUS , GETCAPS , GETMXDS , GETSTATUS_DEF , GETACCCR : begin
                    if(REP_START_COUNT == 1'b0) 
                      begin
                        
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b001    ; 
                        o_crh_pp_od             <= 1'b1      ; //push-pull
                        o_crh_regf_wr_en        <= 1'b0      ;
                        o_crh_regf_rd_en        <= 1'b1      ;
                        o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;
                        state                   <= BROADCAST_ADDR ;
                        REP_START_COUNT         <= REP_START_COUNT + 1'b1 ;
                      end 
                    else if(REP_START_COUNT == 1'b1) 
                      begin
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b001    ;
                        o_crh_cnt_en            <= 1'b1      ;
                        o_crh_pp_od             <= 1'b1      ;
                        o_crh_regf_wr_en        <= 1'b0      ;
                        o_crh_regf_rd_en        <= 1'b1      ;
                        state <= ADDRESS ;
                        REP_START_COUNT <= 1'b0 ;
                      end
                    else
                      begin
                        state <= REP_START ;
                      end
                      
                    end
                    DISEC , ENTASx , DEFTGTS: begin
                      o_crh_rx_en             <= 1'b0      ;
                      o_crh_tx_en             <= 1'b1      ;
                      o_crh_tx_mode           <= 3'b001    ;
                      o_crh_cnt_en            <= 1'b1      ;
                      o_crh_pp_od             <= 1'b1      ; //push-pull
                      o_crh_regf_rd_en        <= 1'b1      ;
                      o_crh_regf_wr_en        <= 1'b0      ;
                      o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;
                      state <= BROADCAST_ADDR ;
                    end

                    endcase

              
            end 
          else
            begin
              state <= REP_START ;
            end 
                  

          end 
          
          
          
          BROADCAST_ADDR : begin 
            o_crh_cnt_en            <= 1'b1      ;
            
            if(i_crh_tx_pp_mode_done)
              begin
                state <= ACK ;
                o_crh_cnt_en         <= 1'b0      ;
                o_crh_pp_od             <= 1'b0      ;
                o_crh_tx_en             <= 1'b0 ;
                o_crh_rx_en             <= 1'b1      ;       
                o_crh_rx_mode           <= 3'b000     ; //ack mode in controller rx
                o_crh_rx_cnt_en         <= 1'b0      ;
                case(int_state)
                 DISEC : begin
                       o_crh_regf_addr <= DISEC_ADDR_REG_FILE     ; 
                         end
                     endcase
              end 
            else
              begin
                state <= BROADCAST_ADDR ;
              end
            end  
           
           
            
          ACK : begin 
                o_crh_regf_rd_en        <= 1'b1      ;
                 o_crh_tx_en             <= 1'b0 ;
                o_crh_rx_en             <= 1'b1      ;       
                o_crh_rx_mode           <= 2'b00     ; //ack mode in controller rx
                o_crh_rx_cnt_en         <= 1'b0      ;
            if(i_crh_rx_mode_done && i_crh_scl_neg_edge)
              begin
                if(!i_crh_rx_nack_ack)
                  begin
                    case(int_state)
                      GETSTATUS , GETCAPS , GETMXDS , GETSTATUS_DEF , GETACCCR : begin
                        if(ACK_COUNT == 2'b00 )
                          begin
                            o_crh_rx_en             <= 1'b0      ;
                            o_crh_tx_en             <= 1'b1      ;
                            o_crh_tx_mode           <= 3'b001    ; 
                            o_crh_cnt_en            <= 1'b1      ;
                            o_crh_regf_rd_en        <= 1'b1      ;
                            o_crh_regf_wr_en        <= 1'b0      ;
                            o_crh_pp_od             <= 1'b1      ;
                            state <= CCC_CODE ;
                            if(int_state == GETSTATUS || int_state == GETSTATUS_DEF)
                              begin
                                o_crh_regf_addr <= GETSTATUS_ADDR_REG_FILE     ; 
                              end
                            else if(int_state == GETCAPS)
                              begin
                                o_crh_regf_addr <= GETCAPS_ADDR_REG_FILE     ; 
                              end
                            else if(int_state == GETMXDS)
                              begin
                                o_crh_regf_addr <= GETMXDS_ADDR_REG_FILE     ; 
                              end
                            else if(int_state == GETACCCR)
                              begin
                                o_crh_regf_addr <= GETACCCR_ADDR_REG_FILE     ; 
                              end
                                
                            ACK_COUNT <= ACK_COUNT + 2'b1 ;
                          end
                        else if(ACK_COUNT == 2'b01)
                          begin
                            o_crh_tx_en             <= 1'b0      ;
                            o_crh_rx_en             <= 1'b1      ;
                            o_crh_rx_mode           <= 3'b001    ; //deserializing mode in controller rx
                            o_crh_rx_cnt_en         <= 1'b1      ;
                            o_crh_cnt_en            <= 1'b1      ;
                            o_crh_pp_od             <= 1'b1      ;
                            o_crh_regf_rd_en        <= 1'b0 ;
                            state <= DATA_RETURNED_1 ;
                            ACK_COUNT <= 2'b0 ;
                          end
                        else 
                          begin
                            state <= ACK ;
                          end 
                      end
                      DISEC , DEFTGTS , ENTASx  : begin
                       o_crh_rx_en             <= 1'b0      ;
                       o_crh_tx_en             <= 1'b1      ;
                       o_crh_tx_mode           <= 3'b001    ; 
                       o_crh_cnt_en            <= 1'b1      ;
                       o_crh_regf_rd_en        <= 1'b1      ;
                       o_crh_regf_wr_en        <= 1'b0      ;
                       o_crh_pp_od             <= 1'b1      ;
                       if(int_state == DISEC)
                          begin
                            o_crh_regf_addr <= DISEC_ADDR_REG_FILE     ; 
                          end
                       else if(int_state == DEFTGTS)
                          begin
                            o_crh_regf_addr <= DEFTGTS_ADDR_REG_FILE     ; 
                          end
                        else if(int_state == ENTASx && i_crh_CRHDLY[1:0] == 2'b00)
                          begin
                            o_crh_regf_addr <= ENTAS0_ADDR_REG_FILE     ; 
                          end
                        else if(int_state == ENTASx && i_crh_CRHDLY[1:0] == 2'b01)
                          begin
                            o_crh_regf_addr <= ENTAS1_ADDR_REG_FILE     ; 
                          end
                        else if(int_state == ENTASx && i_crh_CRHDLY[1:0] == 2'b10)
                          begin
                            o_crh_regf_addr <= ENTAS2_ADDR_REG_FILE     ; 
                          end
                        else if(int_state == ENTASx && i_crh_CRHDLY[1:0] == 2'b11)
                          begin
                            o_crh_regf_addr <= ENTAS3_ADDR_REG_FILE     ; 
                          end
                       state <= CCC_CODE ;
                      end      
                             
                    endcase
                  end
                else
                  begin
                    case(int_state)
                      GETSTATUS : begin
                       if(i_crh_getstatus_data[7:6] == 2'b11)
                          begin
                            //preparing_done <= 1'b1 ;
                            state <= HANDOFF ;
                            o_crh_rx_en             <= 1'b0      ;
                            o_crh_tx_en             <= 1'b1      ;
                            o_crh_tx_mode           <= 3'b010    ; 
                            o_crh_send_stop         <= 1'b1      ;
                            o_crh_pp_od             <= 1'b1      ;
                            //preparing_done          <= 1'b0      ;
                            
                          end
                        else
                          begin
                            o_crh_rx_en             <= 1'b0      ;
                            o_crh_tx_en             <= 1'b1      ;
                            o_crh_tx_mode           <= 3'b110    ;
                            o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                            state <= REP_START ;
                            int_state <= GETCAPS ;                      
                          end
                      end
                      GETCAPS : begin
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b110    ;
                        o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                        state <= REP_START ;
                        int_state <= GETMXDS ;
                      end
                      GETMXDS : begin
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b110    ;
                        o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                        state <= REP_START ;
                        int_state <= DISEC ;
                      end
                      DISEC : begin
                        if(i_crh_CRHDLY[2] == 1'b1)
                            begin
                              o_crh_rx_en             <= 1'b0      ;
                              o_crh_tx_en             <= 1'b1      ;
                              o_crh_tx_mode           <= 3'b110    ;
                              o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                              state <= REP_START ;
                              int_state <= ENTASx ;
                            end
                          else
                            begin
                              state <= REP_START ;
                              int_state <= GETSTATUS_DEF ;
                            end    
                      end
                      ENTASx : begin
                      if(i_crh_CRCAP2[3] || i_crh_CRCAP2[2]) //deep sleep capable + delayed handoff 
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETSTATUS_DEF ;
                        end
                      else 
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETACCCR ;
                        end 
                      end
                      GETSTATUS_DEF : begin
                      if(i_crh_PRECR[0])
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull 
                          state <= REP_START ;
                          int_state <= DEFTGTS ;
                        end
                      else if(i_crh_PRECR[1:0] == 2'b10)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETSTATUS_DEF ;
                        end
                      else if(i_crh_PRECR[1:0] == 2'b00)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull 
                          state <= REP_START ;
                          int_state <= GETACCCR ;
                        end
                      end
                      DEFTGTS : begin
                      if(i_crh_PRECR[1]) 
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETSTATUS_DEF ;
                        end
                      else
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETACCCR ;
                        end
                      end              
                    endcase
              end
            end
            else 
              begin
                state <= ACK ;
              end 
            
          end
          
          
          CCC_CODE: begin 
            
            if(i_crh_tx_pp_mode_done )
              begin
                o_crh_rx_en             <= 1'b0      ;
                o_crh_cnt_en            <= 1'b0      ;
                o_crh_tx_en             <= 1'b1      ;
                o_crh_tx_mode           <= 3'b011    ; 
                o_crh_pp_od             <= 1'b1      ;
                state <= PAR_BIT ; 
              end 
            else
              begin
                state <= CCC_CODE ;
              end 
              
          end
          
          ADDRESS : begin
            if(i_crh_tx_pp_mode_done)
              begin
                o_crh_cnt_en            <= 1'b0      ;
                o_crh_tx_en             <= 1'b0      ;
                o_crh_rx_en             <= 1'b1      ;
                o_crh_rx_mode           <= 2'b00     ; //ack mode in controller rx
                o_crh_rx_cnt_en         <= 1'b0      ;
                o_crh_pp_od             <= 1'b0      ; //open drain
                state <= ACK  ;
              end
            else
              begin
                state <= ADDRESS ;
              end
              
              
            end
          
          
          PAR_BIT : begin
                  
            if(i_crh_tx_pp_mode_done )
              begin
                case(int_state)
                  GETSTATUS : begin
                    if(PAR_BIT_COUNT == 6'd0)
                      begin
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b110    ;
                        o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                        if(i_crh_initiated_request) //address of the target to be sent the controller role 
                           begin
                            o_crh_regf_addr <= TARGET_ADDR_REG_FILE ; //need to be edited
                           end
                          else //address of the target wining the arbitration 
                           begin
                            o_crh_regf_addr <= ARBITRATION_ADDR_REG_FILE  ;
                           end
                        state <= REP_START;
                        PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                      end 
                    else if(PAR_BIT_COUNT == 6'd1)
                      begin
                        o_crh_tx_en             <= 1'b0      ;
                        o_crh_rx_en             <= 1'b1      ;
                        o_crh_rx_mode           <= 3'b001    ; //deserializing mode in controller rx
                        o_crh_pp_od             <= 1'b1      ; 
                        o_crh_regf_rd_en        <= 1'b0      ;
                        state <= DATA_RETURNED_2 ;
                        PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                      end
                    else if(PAR_BIT_COUNT == 6'd2)
                      begin
                        
                        if(i_crh_getstatus_data[7:6] == 2'b11)
                          begin
                            //preparing_done <= 1'b1 ;
                            state <= HANDOFF ;
                            PAR_BIT_COUNT <= 1'b0;
                            o_crh_rx_en             <= 1'b0      ;
                            o_crh_tx_en             <= 1'b1      ;
                            o_crh_tx_mode           <= 3'b010    ; 
                            o_crh_send_stop         <= 1'b1      ;
                            o_crh_pp_od             <= 1'b1      ;
                            //preparing_done          <= 1'b0      ;
                            
                          end
                        else
                          begin
                            o_crh_regf_rd_en        <= 1'b1      ;
                            o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                            o_crh_rx_en             <= 1'b0      ;
                            o_crh_tx_en             <= 1'b1      ;
                            o_crh_tx_mode           <= 3'b110    ;
                            o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                            state <= REP_START ;
                            int_state <= GETCAPS ;     
                            PAR_BIT_COUNT <= 1'b0;                 
                          end
                      end 
                    else
                      begin
                        state <= PAR_BIT ;
                      end
                      
                    end
                    GETCAPS  : begin 
                      if(PAR_BIT_COUNT == 6'd0)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b001    ; 
                          o_crh_cnt_en            <= 1'b1      ;
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_wr_en        <= 1'b0      ;
                          o_crh_pp_od             <= 1'b1      ;
                          o_crh_regf_addr         <= DEF_BYTE_REG_FILE ;
                          state <= DEF_BYTE ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end 
                      else if(PAR_BIT_COUNT == 6'd1)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          if(i_crh_initiated_request) //address of the target to be sent the controller role 
                           begin
                            o_crh_regf_addr <= TARGET_ADDR_REG_FILE ; //need to be edited
                           end
                          else //address of the target wining the arbitration 
                           begin
                            o_crh_regf_addr <= ARBITRATION_ADDR_REG_FILE  ;
                           end
                          state <= REP_START ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end
                      else if(PAR_BIT_COUNT == 6'd2)
                        begin
                          o_crh_tx_en             <= 1'b0      ;
                          o_crh_rx_en             <= 1'b1      ;
                          o_crh_rx_mode           <= 3'b001    ; //deserializing mode in controller rx
                          
                          o_crh_pp_od             <= 1'b1      ;
                          o_crh_regf_rd_en        <= 1'b0      ;
                          state <= DATA_RETURNED_2 ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end
                      else if(PAR_BIT_COUNT == 6'd3)
                        begin
                          //o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                          PAR_BIT_COUNT <= 6'd0 ;
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETMXDS ;
                        end
                      else
                        begin
                          state <= PAR_BIT ;
                        end
                      end 
                    GETMXDS : begin
                      if(PAR_BIT_COUNT == 6'd0)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b001    ; 
                          o_crh_cnt_en            <= 1'b1      ;
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_wr_en        <= 1'b0      ;
                          o_crh_pp_od             <= 1'b1      ;
                          o_crh_regf_addr         <= DEF_BYTE_REG_FILE ;
                          state <= DEF_BYTE ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end 
                      else if(PAR_BIT_COUNT == 6'd1)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          if(i_crh_initiated_request) //address of the target to be sent the controller role 
                           begin
                            o_crh_regf_addr <= TARGET_ADDR_REG_FILE ; //need to be edited
                           end
                          else //address of the target wining the arbitration 
                           begin
                            o_crh_regf_addr <= ARBITRATION_ADDR_REG_FILE  ;
                           end
                          state <= REP_START ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end
                      else if(PAR_BIT_COUNT == 6'd2)
                        begin
                          o_crh_regf_rd_en        <= 1'b1      ;
                        	 o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                          o_crh_rx_en             <= 1'b0      ;
                          PAR_BIT_COUNT <= 6'd0 ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= DISEC ;
                        end
                      else
                        begin
                          state <= PAR_BIT ;
                        end
                      end 
                    DISEC : begin
                      if(PAR_BIT_COUNT == 6'd0)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b001    ; 
                          o_crh_cnt_en            <= 1'b1      ;
                          o_crh_fcnt_en           <= 1'b1      ;
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_wr_en        <= 1'b0      ;
                          o_crh_pp_od             <= 1'b1      ;
                          o_crh_regf_addr <= DISEC_DATA_ADDR_REG_FILE ;
                          state <= DATA_SENT_1 ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end 
                      else if(PAR_BIT_COUNT == 6'd1)
                        begin
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                          PAR_BIT_COUNT <= 6'd0 ;
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          if(i_crh_CRHDLY[2] == 1'b1)
                            begin
                              int_state <= ENTASx ;
                            end
                          else
                            begin
                              int_state <= GETSTATUS_DEF ;
                            end    
                        end
                      else
                        begin
                          state <= PAR_BIT ;
                        end
                        
                      end
                    ENTASx : begin
                      o_crh_timer_set <= 1'b1 ;
                      o_crh_regf_rd_en        <= 1'b1      ;
                      o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                      if(i_crh_CRHDLY[1:0] == 2'b00)
                        begin
                          o_crh_timer_entasx <= 2'b00 ;
                        end
                      else if(i_crh_CRHDLY[1:0] == 2'b01)
                        begin
                          o_crh_timer_entasx <= 2'b01 ;
                        end
                      else if(i_crh_CRHDLY[1:0] == 2'b10)
                        begin
                          o_crh_timer_entasx <= 2'b10 ;
                        end
                      else if(i_crh_CRHDLY[1:0] == 2'b11)
                        begin
                          o_crh_timer_entasx <= 2'b11 ; 
                        end 
                      
                      if(i_crh_CRCAP2[3] || i_crh_CRCAP2[2]) //deep sleep capable + delayed handoff 
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETSTATUS_DEF ;
                        end
                      else 
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          state <= REP_START ;
                          int_state <= GETACCCR ;
                        end 
                      
                    end
                    GETSTATUS_DEF : begin 
                      if(PAR_BIT_COUNT == 6'd0)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b001    ; 
                          o_crh_cnt_en            <= 1'b1      ;
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_wr_en        <= 1'b0      ;
                          o_crh_pp_od             <= 1'b1      ;
                          o_crh_regf_addr         <= DEF_BYTE_REG_FILE ;
                          state <= DEF_BYTE ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end 
                      else if(PAR_BIT_COUNT == 6'd1)
                        begin
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          if(i_crh_initiated_request) //address of the target to be sent the controller role 
                           begin
                            o_crh_regf_addr <= TARGET_ADDR_REG_FILE ; //need to be edited
                           end
                          else //address of the target wining the arbitration 
                           begin
                            o_crh_regf_addr <= ARBITRATION_ADDR_REG_FILE  ;
                           end
                          state <= REP_START ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end
                      else if(PAR_BIT_COUNT == 6'd2)
                        begin
                          o_crh_tx_en             <= 1'b0      ;
                          o_crh_rx_en             <= 1'b1      ;
                          o_crh_rx_mode           <= 3'b001    ; //deserializing mode in controller rx

                          o_crh_pp_od             <= 1'b1      ;
                          state <= DATA_RETURNED_2 ;
                          PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                        end
                      else if(PAR_BIT_COUNT == 6'd3)
                        begin
                          o_crh_regf_rd_en        <= 1'b1      ;
                          o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ;    
                          PAR_BIT_COUNT <= 6'd0 ;
                          o_crh_rx_en             <= 1'b0      ;
                          o_crh_tx_en             <= 1'b1      ;
                          o_crh_tx_mode           <= 3'b110    ;
                          o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                          if(i_crh_PRECR[0])
                            begin
                              state <= REP_START ;
                              int_state <= DEFTGTS ;
                            end
                          else if(i_crh_PRECR[1:0] == 2'b10)
                            begin
                              state <= REP_START ;
                              int_state <= GETSTATUS_DEF ;
                            end
                          else if(i_crh_PRECR[1:0] == 2'b00)
                            begin
                              state <= REP_START ;
                              int_state <= GETACCCR ;
                            end
                        end
                      else
                        begin
                          state <= PAR_BIT ;
                        end
                    end
                    DEFTGTS : begin 
                      
                      
                          if( PAR_BIT_COUNT == ((i_crh_tgts_count+1)*4 + 1) )
                            begin
                              DATA_SENT_COUNT <= 6'd0 ;
                              counter <= 6'd1 ;
                              PAR_BIT_COUNT           <= 6'b0      ;
                              o_crh_rx_en             <= 1'b0      ;
                              o_crh_tx_en             <= 1'b1      ;
                              o_crh_tx_mode           <= 3'b110    ;
                              o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                              o_crh_regf_rd_en        <= 1'b1      ;
                              o_crh_regf_addr         <= BROADCAST_ADDR_REG_FILE  ; 
                              if(i_crh_PRECR[1]) 
                                begin
                                  state <= REP_START ;
                                  int_state <= GETSTATUS_DEF ;
                                end
                              else
                                begin
                                  state <= REP_START ;
                                  int_state <= GETACCCR ;
                                end
                            end
                          else 
                            begin
                              PAR_BIT_COUNT           <= PAR_BIT_COUNT + 1'b1 ; 
                              DATA_SENT_COUNT         <= DATA_SENT_COUNT + 1'b1 ;
                              o_crh_rx_en             <= 1'b0      ;
                              o_crh_tx_en             <= 1'b1      ;
                              o_crh_tx_mode           <= 3'b001    ; 
                              o_crh_cnt_en            <= 1'b1      ;
                              o_crh_fcnt_en           <= 1'b1      ;
                              o_crh_regf_rd_en        <= 1'b1      ;
                              o_crh_regf_wr_en        <= 1'b0      ;
                              o_crh_pp_od             <= 1'b1      ;
                              state <= DATA_SENT_1 ; 
                              if( DATA_SENT_COUNT == 6'd0 )
                                begin
                                  o_crh_regf_addr <= 9'd35    ;
                                end
                              else if (DATA_SENT_COUNT == 6'd1)
                                begin
                                  o_crh_regf_addr <= 9'd35    ; //active controller DA (need to be edited)
                                end
                              else if (DATA_SENT_COUNT == 6'd2)
                                begin
                                  o_crh_regf_addr <= 9'd35    ;  //active controller DCR (need to be edited)
                                end
                              else if (DATA_SENT_COUNT == 6'd3)
                                begin
                                	 o_crh_regf_addr <= 9'd35    ; //active controller BCR ( need to be edited) 
                                end
                              else if(DATA_SENT_COUNT == 6'd4)
                                begin
                                  o_crh_regf_addr <= BROADCAST_ADDR_REG_FILE ;
                                end
                              else if(DATA_SENT_COUNT == counter*4 + 6'd1)
                                  begin
                                    o_crh_regf_addr <= 9'd199 +  counter*9   ;
                                  end 
                              else if(DATA_SENT_COUNT == counter*4 + 6'd2)
                                  begin 
                                  	 o_crh_regf_addr <= 9'd198 + counter*9    ;
                                  end
                              else if(DATA_SENT_COUNT == counter*4 + 6'd3)
                                  begin
                                    o_crh_regf_addr <= 9'd197 + counter*9    ;
                                  end
                              else if(DATA_SENT_COUNT == counter*4 + 6'd4)
                                  begin
                                    o_crh_regf_addr <= 9'd199 + counter*9    ; //need to be edited
                                    counter <= counter + 1 ;
                                  end
                            end //end of the else
                  //counter <= 6'd1 ;
                      //PAR_BIT_COUNT <= 6'd0 ;
                    end // end of the state 
                    GETACCCR : begin
                    if(PAR_BIT_COUNT == 6'd0)
                      begin
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b110    ;
                        o_crh_pp_od             <= 1'b1      ; //rep start is push pull
                        if(i_crh_initiated_request) //address of the target to be sent the controller role 
                           begin
                            o_crh_regf_addr <= TARGET_ADDR_REG_FILE ; //need to be edited
                           end
                          else //address of the target wining the arbitration 
                           begin
                            o_crh_regf_addr <= ARBITRATION_ADDR_REG_FILE  ;
                           end
                        state <= REP_START;
                        PAR_BIT_COUNT <= PAR_BIT_COUNT + 6'd1 ;
                      end 
                    else if(PAR_BIT_COUNT == 6'd1)
                      begin
                        state <= HANDOFF ;
                        PAR_BIT_COUNT <= 6'd0 ;
                        //preparing_done <= 1'b1 ;
                        o_crh_rx_en             <= 1'b0      ;
                        o_crh_tx_en             <= 1'b1      ;
                        o_crh_tx_mode           <= 3'b010    ; 
                        o_crh_send_stop         <= 1'b1      ;
                        o_crh_pp_od             <= 1'b1      ;
                        //preparing_done          <= 1'b0      ;
                      
                      end
                    end
               endcase
              end
            else
              begin
                state <= PAR_BIT ;
              end

          end
          
          
          DEF_BYTE : begin 
            
            if(i_crh_tx_pp_mode_done)
              begin
                o_crh_cnt_en            <= 1'b0      ;
                o_crh_rx_en             <= 1'b0      ;
                o_crh_tx_en             <= 1'b1      ;
                o_crh_tx_mode           <= 3'b011    ; 
                o_crh_pp_od             <= 1'b1      ;
                state <= PAR_BIT ;
              end 
            else
              begin
                state <= DEF_BYTE ;
              end 
              
          end
          
          
         
          DATA_RETURNED_1 : begin
            //data will be saved in reg file depending on the CCC command 
            case(int_state)
                  GETSTATUS : begin 
                    o_crh_regf_wr_en <= 1'b1 ;
                    o_crh_regf_addr <= GETSTATUS_MSB_ADDR_REG_FILE ;
                    o_crh_regf_rd_en <= 1'b0 ;
                  end
                  GETCAPS : begin
                    o_crh_regf_wr_en <= 1'b1 ;
                    o_crh_regf_addr <= CRCAPS1_ADDR_REG_FILE ;
                    o_crh_regf_rd_en <= 1'b0 ;
                
                  end
                  GETMXDS : begin
                    o_crh_regf_wr_en <= 1'b1 ;
                    o_crh_regf_addr <= CRHDLY1_ADDR_REG_FILE ;
                    o_crh_regf_rd_en <= 1'b0 ;
                
                  end
                endcase 


            if(i_crh_rx_pp_mode_done ) 
              begin
                o_crh_rx_cnt_en         <= 1'b0      ;
                o_crh_cnt_en            <= 1'b0      ;
                o_crh_rx_en             <= 1'b0      ;
                o_crh_tx_en             <= 1'b1      ;
                o_crh_tx_mode           <= 3'b011    ; 
                o_crh_pp_od             <= 1'b1      ;
                o_crh_regf_wr_en <= 1'b0 ;
                o_crh_regf_rd_en <= 1'b1 ;
                state <= PAR_BIT ;
              end 
            else
              begin
                state <= DATA_RETURNED_1 ;
              end 
              
              
            end
              
           DATA_RETURNED_2 : begin 
             o_crh_rx_cnt_en         <= 1'b1      ;
             o_crh_cnt_en            <= 1'b1      ;
                case(int_state)
                   GETSTATUS : begin 
                     o_crh_regf_rd_en <= 1'b0 ;
                     o_crh_regf_wr_en <= 1'b1 ;
                     o_crh_regf_addr <= GETSTATUS_LSB_ADDR_REG_FILE;
                   end
                   GETCAPS : begin 
                     o_crh_regf_rd_en <= 1'b0 ;
                     o_crh_regf_wr_en <= 1'b1 ;
                     o_crh_regf_addr <= CRCAPS2_ADDR_REG_FILE  ;
                   end
                   GETSTATUS_DEF : begin
                     o_crh_regf_rd_en <= 1'b0 ;
                     o_crh_regf_wr_en <= 1'b1 ;
                     o_crh_regf_addr <= PRECR_ADDR_REG_FILE ; 
                   end
                endcase
                
             if(i_crh_rx_pp_mode_done)
               begin
                 o_crh_cnt_en            <= 1'b0      ;
                 o_crh_rx_cnt_en         <= 1'b0      ;
                 o_crh_rx_en             <= 1'b0      ;
                 o_crh_tx_en             <= 1'b1      ;
                 o_crh_tx_mode           <= 3'b011    ; 
                 o_crh_pp_od             <= 1'b1      ;
                 o_crh_regf_wr_en        <= 1'b0 ;
                 o_crh_regf_rd_en        <= 1'b1 ; 
                 state                   <= PAR_BIT ;
               end
               
             else
               begin
                 state <= DATA_RETURNED_2 ;
               end
               
               
             end
             DATA_SENT_1 : begin
               
               if(i_crh_tx_pp_mode_done)
                 begin
                   o_crh_cnt_en            <= 1'b0      ;
                   o_crh_rx_en             <= 1'b0      ;
                   o_crh_tx_en             <= 1'b1      ;
                   o_crh_tx_mode           <= 3'b011    ; 
                   o_crh_pp_od             <= 1'b1      ;
                   state <= PAR_BIT ;
                 end
               else
                 begin
                   state <= DATA_SENT_1 ;
                 end
                       
                       
                       
             end
             HANDOFF : begin 
               
               /*if(preparing_done)
                 begin
                   o_crh_rx_en             <= 1'b0      ;
                   o_crh_tx_en             <= 1'b1      ;
                   o_crh_tx_mode           <= 3'b010    ; 
                   o_crh_send_stop         <= 1'b1      ;
                   o_crh_pp_od             <= 1'b1      ;
                   preparing_done          <= 1'b0      ;
                 end
               else */if(i_crh_stop_is_sent)
                 begin
                   o_crh_send_stop         <= 1'b0      ;
                   o_crh_scl_idle <= 1'b1 ;
                   o_crh_pp_od    <= 1'b0 ;
                   stop_is_sent <= 1'b1 ; 
                 end 
               else
                 begin
                   o_crh_send_stop         <= 1'b0      ;
                   state <= HANDOFF ;
                 end 
                 
                 
              if(!i_crh_crhpoverlap && stop_is_sent ) //overlap condition
                begin
                  o_crh_tx_en             <= 1'b0      ;
                  o_crh_tx_mode           <= 3'b111    ; //high-z 
                end
              else if(i_crh_crhpoverlap && stop_is_sent )
                begin
                  state                     <= TESTING   ;
                  //o_crh_ncr_take_control        <= 1'b1      ; //ncr will take the tx and rx and regfile   
                end
              else
                 begin
                   state <= HANDOFF ;
                 end 
                                
               end
            TESTING : begin 
               
               if(i_crh_newcrlock) //
                 begin
                   o_crh_scl_idle          <= 1'b0      ;
                   o_crh_tx_en             <= 1'b0      ;
                   o_crh_rx_en             <= 1'b1      ;
                   o_crh_rx_mode           <= 3'b110    ; //T_bit mode in controller rx (check for start)
                   if(i_crh_rx_mode_done ) 
                     begin
                       if(i_crh_start_detected) //new controller pulled sda low 
                         begin
                           state                   <= IDLE      ;
                           //o_crh_ncr_win           <= 1'b1      ; //ncr asserted the controller role 
                           o_crh_scl_idle          <= 1'b0      ;
                           o_crh_done              <= 1'b1      ;
                         end
                       else if(!i_crh_start_detected && i_crh_scl_pos_edge) //new controller didn't pull sda low & former controller needs to drive sda low 
                         begin
                           o_crh_rx_en             <= 1'b0      ;
                           o_crh_tx_en             <= 1'b1      ;
                           o_crh_tx_mode           <= 3'b111    ; //sda being pulled low 
                           state                   <= MONITOR  ;
                         end
                     end
                 end
                         
               end
            MONITOR : begin
              if(i_crh_sda_low)
                begin
                  if(!i_crh_timer_cas) //need to be edited to 100us or higher 
                    begin
                      if(i_crh_scl_neg_edge) //new controller pulled the scl low
                        begin
                          state                   <= IDLE ;
                          //o_crh_ncr_win           <= 1'b1      ; //ncr asserted the controller role 
                          o_crh_done              <= 1'b1      ;
                          dont_repeat             <= 1'b1      ;
                          o_crh_scl_idle          <= 1'b0      ;
                          o_crh_tx_en             <= 1'b0      ;
                        end
                      /* else //new controller didn't pull the scl low
                        begin
                          state                   <= IDLE ;
                          o_crh_ncr_win           <= 1'b0      ; //ncr didn't assert the controller role 
                          o_crh_done              <= 1'b1      ;
                          o_crh_scl_idle          <= 1'b0      ;
                          o_crh_tx_en             <= 1'b0      ;
                        end */
                    end
                  else
                    begin
                          state                   <= IDLE ;
                          //o_crh_ncr_win           <= 1'b0      ; //ncr didn't assert the controller role 
                          o_crh_done              <= 1'b1      ;
                          dont_repeat             <= 1'b1      ;
                          o_crh_scl_idle          <= 1'b0      ;
                          o_crh_tx_en             <= 1'b0      ;
                      end
                       
                    end
                end  
                       
             
           endcase
    end
  end 
endmodule

`default_nettype wire          

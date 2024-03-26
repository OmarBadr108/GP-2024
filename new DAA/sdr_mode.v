//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Nour Eldeen Samir , Youssef Essam , Mostafa Hassan , Yaseen Salah , Zyad Sobhy
// Revision: Yaseen Salah , Nour Eldeen Samir 
//
// Version : 1.0
// 
// Create Date:  7:46 PM     12/15/2022 
// Design Name:  sdr_controller
// Module Name:  sdr_controller 
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
module sdr_mode(
    input  wire          i_sdr_ctrl_clk                ,
    input  wire          i_sdr_ctrl_rst_n              ,
    input  wire          i_sdr_ctrl_cnt_done           , //need naming revisited 
    input  wire          i_i3c_ctrl_sdr_en             , //mod in top module
    input  wire          i_sdr_ctrl_last_frame         ,
    input  wire          i_ser_mode_done               , 
    input  wire          i_deser_mode_done             ,
    input  wire          i_sdr_regf_rx_tx              , //RnW bit from serializer, 1 = rx , 0 = tx 
    input  wire          i_ser_nack_ack                , // 1 = no acknoledge 0 = ACK 
    input  wire          i_sdr_rx_rd_abort             ,
    input  wire          i_ser_to_par_trans            , // 1 only at the serializing state of the tx, otherwise 0
    input  wire          i_sdr_ctrl_bit_cnt_done       , // bits count done , output from bits counter
    input  wire          i_sdr_ctrl_scl_neg_edge       ,
    input  wire          i_sdr_ctrl_scl_pos_edge       ,
    input  wire          i_sdr_ctrl_scl_stall_done     ,
    input  wire          i_sdr_ctrl_ibi_payload_en     ,
    
    
    input  wire          i_sdr_rx_arbitration_lost     ,
    output reg           o_sdr_ctrl_scl_stall_flag     ,
    output reg   [3:0]   o_sdr_ctrl_scl_stall_cycles   ,
    output reg           o_sdr_ctrl_scl_idle           ,
    output reg           o_sdr_ctrl_fcnt_en            ,
    output reg           o_sdr_ctrl_ser_en             ,
    output reg           o_sdr_ctrl_ser_valid          ,
    output reg   [2:0]   o_sdr_ctrl_ser_mode           ,
    output reg           o_sdr_ctrl_deser_en           ,
    output reg   [2:0]   o_sdr_rx_mode                 , // deser mode before
    output reg           o_sdr_ctrl_cnt_en             ,
    output reg           o_sdr_ctrl_rx_cnt_en          ,
    output reg           o_sdr_ctrl_pp_od              ,
    output reg           o_sdr_ctrl_addr_done          , 
    output reg           o_sdr_ctrl_done               ,
    output reg           o_sdr_ctrl_regf_wr_en         ,
    output reg           o_sdr_ctrl_regf_rd_en_pulse   ,
    output reg   [11:0]   o_sdr_ctrl_regf_addr          ,
    output reg           o_sdr_ctrl_payload_done       ,
    output reg           o_sdr_ctrl_rx_valid            // need to be parametrized using define   
    );
/////////////////////ADDRESS PARAMTERES///////////////////////
localparam IBI_PAYLOAD_BASE_ADDRESS = 108;

//- states encoding in gray ----------------------------------------------

localparam SDR_IDLE     = 4'b0000 ; 
localparam ADDRESS      = 4'b0011 ;
localparam ACK_BIT      = 4'b0010 ;
localparam HANDOFF      = 4'b0110 ;
localparam SCL_STALLING = 4'b0111 ;
localparam DATA_OUT     = 4'b0101 ;
localparam DATA_IN      = 4'b0100 ;
localparam PARITY_BIT   = 4'b1100 ;
localparam T_BIT        = 4'b1101 ;


//-- internal wires declaration ------------------------------------------

reg [3:0] state                  ;
reg       address_ack_state_flag ; //Used to go to handoff state where we handle special cases transitions like last bit in Address and from Address to Ack
reg       sdr_rx_rd_abort_extend ;

//Pulse Generator
reg  i_ser_mode_done_prev         ;
reg  i_deser_mode_done_prev       ;
wire i_ser_mode_done_pulse        ;
wire i_deser_mode_done_pulse      ;
wire i_deser_mode_done_pulse_tbit ;
wire ser_mode_done_mux_out        ;

assign ser_mode_done_mux_out = (i_ser_to_par_trans)? i_sdr_ctrl_bit_cnt_done : i_ser_mode_done ;

always@(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
    begin
        if (!i_sdr_ctrl_rst_n) 
            begin
                i_ser_mode_done_prev   <= 1'b0 ;
                i_deser_mode_done_prev <= 1'b0 ;
            end
        else
            begin    
                i_ser_mode_done_prev   <= ser_mode_done_mux_out ;
                i_deser_mode_done_prev <= i_deser_mode_done     ;
            end
    end
assign i_ser_mode_done_pulse   = ~(i_ser_mode_done_prev)   & ser_mode_done_mux_out ; 
assign i_deser_mode_done_pulse = ~(i_deser_mode_done_prev) & i_deser_mode_done     ;  
  
  
//Pulse from the pulse Generator // need to remove i_
reg  i_ser_mode_done_prev3          ;
reg  i_deser_mode_done_prev3        ;

reg  i_ser_mode_done_prev2          ;
reg  i_deser_mode_done_prev2        ;

wire i_ser_mode_done_pulse_parity   ;

//needs reset.. // to be revised
always@(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
    begin
        if (!i_sdr_ctrl_rst_n) 
            begin
                i_ser_mode_done_prev2   <= 1'b0;
                i_ser_mode_done_prev3   <= 1'b0;
                i_deser_mode_done_prev2 <= 1'b0;
                i_deser_mode_done_prev3 <= 1'b0;
            end
        else
            begin    
                i_ser_mode_done_prev2   <= i_ser_mode_done_pulse   ;
                i_deser_mode_done_prev2 <= i_deser_mode_done_pulse ;  

                i_ser_mode_done_prev3   <= i_ser_mode_done_prev2   ;
                i_deser_mode_done_prev3 <= i_deser_mode_done_prev2 ;
            end
    end
    
assign i_ser_mode_done_pulse_parity = i_ser_mode_done_prev3   & ~(i_ser_mode_done_pulse)   ;
assign i_deser_mode_done_pulse_tbit = i_deser_mode_done_prev3 & ~(i_deser_mode_done_pulse) ;
  
// Pulse for RegFile Read Enable in order to read only 1 frame at a time  // need to remove o_
reg o_sdr_ctrl_regf_rd_en;
reg o_sdr_ctrl_regf_rd_en_prev;
  
always@(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n )
    begin
    if (!i_sdr_ctrl_rst_n) 
      o_sdr_ctrl_regf_rd_en_prev  <= 1'b0;
    else    
      o_sdr_ctrl_regf_rd_en_prev  <=   o_sdr_ctrl_regf_rd_en                               ;  
      o_sdr_ctrl_regf_rd_en_pulse <= ~(o_sdr_ctrl_regf_rd_en_prev) & o_sdr_ctrl_regf_rd_en ;
    end
  

//-- sdr mode main fsm ---------------------------------------------------

always @(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n) 
  begin: sdr_mode_main_fsm
    
    if (!i_sdr_ctrl_rst_n) 
      begin
      //-- state  
        state                        <= SDR_IDLE  ; 
      //-- outputs   
        o_sdr_ctrl_fcnt_en           <= 1'b0      ;
        o_sdr_ctrl_ser_en            <= 1'b0      ;
        o_sdr_ctrl_ser_valid         <= 1'b0      ;
        o_sdr_ctrl_ser_mode          <= 2'b0      ;
        o_sdr_ctrl_deser_en          <= 1'b0      ;
        o_sdr_ctrl_cnt_en            <= 1'b0      ;
        o_sdr_ctrl_pp_od             <= 1'b0      ;
        o_sdr_ctrl_done              <= 1'b0      ;
        o_sdr_rx_mode                <= 2'b0      ;
        o_sdr_ctrl_addr_done         <= 1'b0      ;
        o_sdr_ctrl_regf_rd_en        <= 1'b0      ;
        o_sdr_ctrl_regf_wr_en        <= 1'b0      ;  // write enable output to reg file 
        address_ack_state_flag       <= 1'b0      ;
        o_sdr_ctrl_rx_cnt_en         <= 1'b0      ;
        //o_sdr_ctrl_regf_addr         <= 6'b000000 ; we dont want it to drive the reg file when it is in the idle state and we arent using it 
        o_sdr_ctrl_rx_valid          <= 1'b0      ;
        sdr_rx_rd_abort_extend       <= 1'b0      ;
        o_sdr_ctrl_payload_done      <= 1'b0      ;
        //o_sdr_ctrl_scl_idle          <= 1'b0      ;  we dont need to close scl from here but from the main ctrl unit
      end

    else 
      begin
        case (state) 
          SDR_IDLE:      
            begin 
              o_sdr_ctrl_fcnt_en           <= 1'b0 ;
              o_sdr_ctrl_ser_en            <= 1'b0 ;
              o_sdr_ctrl_ser_valid         <= 1'b0 ;
              o_sdr_ctrl_ser_mode          <= 2'b0 ;
              //o_sdr_ctrl_deser_en          <= 1'b0 ;  we need ser to be on arbitration
              //o_sdr_ctrl_cnt_en            <= 1'b0 ;
              //o_sdr_ctrl_pp_od             <= 1'b0 ;
              //o_sdr_ctrl_done              <= 1'b0 ;
              //o_sdr_rx_mode                <= 1'b0 ;
              //o_sdr_ctrl_rx_valid          <= 1'b0 ;
              //sdr_rx_rd_abort_extend       <= 1'b0 ;
              //o_sdr_ctrl_scl_idle          <= 1'b1 ;

              if (i_i3c_ctrl_sdr_en)
                begin 
                  state <= ADDRESS ;
                   o_sdr_ctrl_regf_addr         <=  12'b000000   ; 
                   o_sdr_ctrl_pp_od       <= 1'b0   ; 

                end 
              else if (i_sdr_ctrl_ibi_payload_en)
                begin 
                  state <= DATA_IN  ;
                  o_sdr_ctrl_regf_addr  <= IBI_PAYLOAD_BASE_ADDRESS ; // index 108
                end       
              else 
                begin 
                  state <= SDR_IDLE  ;
                end                   
            end 

          ADDRESS:      
            begin 
              o_sdr_ctrl_pp_od       <= 1'b0   ; //Address is driven by OD (not optimized)
              o_sdr_ctrl_ser_mode    <= 2'b01  ; //SERIALIZING mode at Tx             
              o_sdr_ctrl_ser_en      <= 1'b1   ; //Tx Enable 
              o_sdr_ctrl_ser_valid   <= 1'b0   ; //No Data Valid to prevent overwriting the data being serialized
              o_sdr_ctrl_cnt_en      <= 1'b1   ; //Bit Counter Enable
              o_sdr_ctrl_regf_rd_en  <= 1'b1   ;
              address_ack_state_flag <= 1'b1   ;
              o_sdr_ctrl_scl_idle    <= 1'b0   ;

              /// for arbitration //
              o_sdr_ctrl_deser_en <= 1'b1  ; 
              o_sdr_rx_mode       <= 2'b10 ;      ///// arbitration 


              if (i_sdr_rx_arbitration_lost)
                begin 
                  state                <= SDR_IDLE;
                  o_sdr_ctrl_regf_addr <= 12'd48;
                end
              else if (i_ser_mode_done_pulse)
                begin 
                   o_sdr_ctrl_addr_done <= 1'b1    ;
                   state                <= HANDOFF ;                 
                end 
              else 
                begin
                   o_sdr_ctrl_addr_done <= 1'b0    ; 
                   state                <= ADDRESS ;
                end 
            end 
            
          HANDOFF:   
            begin
            if (i_sdr_ctrl_scl_neg_edge && address_ack_state_flag)
                begin
                    o_sdr_ctrl_cnt_en <= 1'b0  ; //Bit Counter Disable
                    state <= ACK_BIT  ;
                end                
            else if  (i_sdr_ctrl_scl_neg_edge && !address_ack_state_flag)  
                begin    
                    if (i_ser_nack_ack) 
                        begin
                            state <= SDR_IDLE;              //STOP after NACK
                            o_sdr_ctrl_scl_idle  <= 1'b1 ;
                            o_sdr_ctrl_ser_mode <=  2'b10 ; //STOP mode 
                             o_sdr_ctrl_done <= 1'b1;
                             o_sdr_ctrl_payload_done <= 1'b1;
                        end    
                    else
                        begin
                            if (i_sdr_regf_rx_tx)
                                begin
                                    state                 <= DATA_IN ;          //Receiving Data at Rx
                                    o_sdr_ctrl_regf_wr_en <= 1'b1      ; // enable reg file to write 
                                    o_sdr_ctrl_regf_addr  <= 12'b010011 ; // 1st frame to be written in RegFile at index 19 
                                    o_sdr_ctrl_ser_en            <= 1'b0  ;
                                end
                            else 
                                begin
                                    state <= SCL_STALLING ;     //Transmitting Data at Tx 
                                end
                        end
                end     
            else 
                begin 
                   state <= HANDOFF  ;
                end              
            end
        
          SCL_STALLING:   
                  begin
                    if (i_sdr_ctrl_scl_stall_done)  
                        begin
                          state <= DATA_OUT;
                          o_sdr_ctrl_ser_mode   <= 2'b01 ;   //SERIALIZING mode at Tx
                        end                                         
                    else
                      begin  
                        o_sdr_ctrl_scl_stall_flag   <= 1'b1      ;  
                        o_sdr_ctrl_scl_stall_cycles <= 4'd6      ;
                        o_sdr_ctrl_ser_en           <= 1'b1      ; //Tx Enable
                        o_sdr_ctrl_regf_rd_en       <= 1'b1      ;
                        o_sdr_ctrl_regf_addr        <= 12'b000010 ; // 1st frame of data in RegFile at index 2.
                        state <= SCL_STALLING; //----------added recently
                      end                      
                  end
        
          ACK_BIT:      
            begin             
              o_sdr_ctrl_pp_od       <= 1'b0  ; //ACK bit is driven by OD
              o_sdr_rx_mode          <= 2'b00 ; //ACK mode at Rx
              o_sdr_ctrl_ser_en      <= 1'b0  ; //Tx Disable 
              //o_sdr_ctrl_cnt_en      <= 1'b0  ; //Bit Counter Disable
              o_sdr_ctrl_rx_cnt_en   <= 1'b0  ; 
              o_sdr_ctrl_deser_en    <= 1'b1  ; //Rx Enable 
              address_ack_state_flag <= 1'b0  ; 
             /* if (i_sdr_regf_rx_tx)               
                  begin // 1 >> rx
                      state <= DATA_IN;                    //Recieving Data at Rx
                      
                  end     
              else
                  begin*/
                      state <= HANDOFF ; //Transmitting Data at Tx                       
                  //end     
            end

          DATA_OUT:      
            begin    
              o_sdr_ctrl_pp_od      <= 1'b1 ; //DATA is driven by PP     //we need to check the handoff
              o_sdr_ctrl_fcnt_en    <= 1'b0 ; //Frame Counter Enable
              o_sdr_ctrl_deser_en   <= 1'b0 ; //Rx Disable             
              o_sdr_ctrl_ser_valid  <= 1'b0 ; //No Data Valid to prevent overwriting the data being serialized  
              o_sdr_ctrl_cnt_en     <= 1'b1 ; //Bit Counter Enable
              o_sdr_ctrl_regf_rd_en <= 1'b0 ;
              
              if (i_ser_mode_done_pulse) 
               begin
                 state <= PARITY_BIT;
                 o_sdr_ctrl_ser_mode <= 2'b11 ; //PARITY mode at Tx                  
               end  
             else
               begin
                 state <= DATA_OUT; 
               end                
           
            end 

          DATA_IN:      
            begin
              o_sdr_rx_mode                <= 2'b01 ;
              o_sdr_ctrl_fcnt_en           <= 1'b0  ;
              o_sdr_ctrl_ser_en            <= 1'b0  ;
              o_sdr_ctrl_deser_en          <= 1'b1  ;
              o_sdr_ctrl_pp_od             <= 1'b1  ;
              o_sdr_ctrl_cnt_en            <= 1'b1  ; //Bit Counter Enable
              o_sdr_ctrl_rx_cnt_en         <= 1'b1  ; // rx counter enable 
              o_sdr_ctrl_regf_wr_en        <= 1'b0  ;
              o_sdr_ctrl_rx_valid          <= 1'b0  ;    

              if (i_deser_mode_done && i_sdr_ctrl_scl_neg_edge)//(i_deser_mode_done_pulse && i_sdr_ctrl_scl_neg_edge)  //(i_deser_mode_done_prev3)  
                begin 
                    o_sdr_ctrl_rx_valid <= 1'b1 ;
                    state <= T_BIT;
                end 
              else 
                begin
                  state <= DATA_IN; 
                end 
            end

          T_BIT:      
            begin
              o_sdr_rx_mode                <= 2'b11 ;
              o_sdr_ctrl_fcnt_en           <= 1'b1  ;
              o_sdr_ctrl_ser_en            <= 1'b0  ;
              o_sdr_ctrl_ser_valid         <= 1'b0  ;
              o_sdr_ctrl_deser_en          <= 1'b1  ;
              o_sdr_ctrl_cnt_en            <= 1'b0  ;
              o_sdr_ctrl_rx_cnt_en         <= 1'b0  ;
              o_sdr_ctrl_pp_od             <= 1'b1  ;
              o_sdr_ctrl_rx_valid          <= 1'b0  ;
              sdr_rx_rd_abort_extend       <= i_sdr_rx_rd_abort ;
                            
              if (i_deser_mode_done && i_sdr_ctrl_scl_neg_edge)
                begin
                  if (sdr_rx_rd_abort_extend) 
                    begin 
                    state <= SDR_IDLE ;
                    o_sdr_ctrl_done      <= 1'b1;
                    o_sdr_ctrl_regf_wr_en <= 1'b1;
                    o_sdr_ctrl_ser_en      <=  1'b0 ; 
                    o_sdr_ctrl_pp_od       <= 1'b1 ;
                    sdr_rx_rd_abort_extend <= 1'b0 ;
                    o_sdr_ctrl_payload_done <= 1'b1;
                    end 
                  else 
                    begin 
                      state <= DATA_IN;
                      o_sdr_ctrl_regf_wr_en <= 1'b1;
                      o_sdr_ctrl_regf_addr  <= o_sdr_ctrl_regf_addr + 1'b1 ;
                    end 
                end
              else 
                begin 
                  state <= T_BIT;
                end 

            end       

          PARITY_BIT:      
            begin
              o_sdr_ctrl_pp_od        <= 1'b1  ; //DATA is driven by PP     //we need to check the handoff       
              o_sdr_ctrl_fcnt_en      <= 1'b0  ; //Frame Counter Disable
              o_sdr_ctrl_ser_en       <= 1'b1  ; //Tx Enable
              o_sdr_ctrl_cnt_en       <= 1'b0  ; //Bit Counter Disable
              
              
              if (i_ser_mode_done_pulse_parity) //(i_ser_mode_done && i_sdr_ctrl_scl_pos_edge ) Edit by Zyad
               begin
                 if(i_sdr_ctrl_last_frame) 
                   begin
                     state <= SDR_IDLE;   //End Write Data Operation
                     o_sdr_ctrl_deser_en          <= 1'b0     ;
                     o_sdr_ctrl_ser_en            <=  1'b1  ; //Tx Enable
                     o_sdr_ctrl_pp_od       <= 1'b1 ;
                     sdr_rx_rd_abort_extend <= 1'b0 ;
                     o_sdr_ctrl_payload_done <= 1'b1;
                     o_sdr_ctrl_done <= 1'b1;
                   end
                 else
                   begin
                     state <= DATA_OUT;   //Write another Frame                
                     o_sdr_ctrl_ser_mode   <= 2'b01; //SERIALIZING mode at Tx
                     o_sdr_ctrl_regf_rd_en   <= 1'b1  ; 
                     o_sdr_ctrl_regf_addr <= o_sdr_ctrl_regf_addr + 1'b1; //increment the address to Read the next data frame from RegFile
                   end
               end  
              else
               begin
                 state <= PARITY_BIT; 
               end                           
            end                                 
        endcase
      end
  end 


endmodule

`default_nettype wire
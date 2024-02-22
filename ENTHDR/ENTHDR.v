/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Omar Maghraby, Laila Tamer 
 
 Revision:   

 Version : 1.0

 Create Date: 
 Design Name:  
 Module Name:  

==================================================================================

  STATEMENT OF USE

  This information contains confidential and proprietary information of MIXEL.
  No part of this information may be reproduced, transmitted, transcribed,
  stored in a retrieval system, or translated into any human or computer
  language, in any form or by any means, electronic, mechanical, magnetic,
  optical, chemical, manual, or otherwise, without the prior written permission
  of MIXEL.  This information was prepared for Garduation Project purpose and is for
  use by MIXEL Engineers only.  MIXEL and ASU 2023 GP reserves the right 
  to make changes in the information at any time and without notice.

==================================================================================
//////////////////////////////////////////////////////////////////////////////////*/

module enthdr (
  input   wire             i_clk           ,
  input   wire             i_rst_n         ,
  input   wire             i_i3cengine_en  ,
  input   wire             i_tx_mode_done  ,
  input   wire             i_rx_ack_nack   ,
  input   wire             i_scl_neg_edge  ,
  input   wire             i_rx_mode_done  ,
  input   wire             i_scl_pos_edge  ,
  
  output  wire             o_pp_od         , 
  output  reg              o_bit_cnt_en    ,   
  output  reg              o_regf_rd_en    ,
  output  reg     [9:0]    o_regf_addr     ,
  output  reg              o_tx_en         ,
  output  reg     [2:0]    o_tx_mode       ,
  output  reg              o_rx_en         ,
  output  reg     [2:0]    o_rx_mode       ,
  output  reg              o_i3cengine_done       // Flag to indicate that the CCC is sent               
  );


 //----------------Internal Signals----------------//
 
 reg [2:0] state;
 
 
 //----------------States Encoding----------------//
 localparam IDLE         = 3'b000 ;
 localparam BROADCAST    = 3'b001 ;
 localparam ACK          = 3'b011 ;
 localparam ENTHDR_DDR   = 3'b010 ;
 localparam PARITY       = 3'b110 ; 
 
 

 assign o_pp_od = 1'b0  ; 



 //----------------ENTHDR0 CCC FSM----------------//
 always@(posedge i_clk or negedge i_rst_n)
   begin
     if(!i_rst_n)
       begin
         state <= IDLE;
         o_regf_rd_en        <= 1'b0;
         o_tx_en             <= 1'b0;
         o_rx_en             <= 1'b0;
         o_i3cengine_done    <= 1'b0;
         o_tx_mode           <= 3'b0;
         o_rx_mode           <= 3'b0;
         o_regf_addr         <= 10'b0;
         o_bit_cnt_en        <= 1'b0;
       end
     else 
       begin
         o_regf_rd_en        <= 1'b0;
         o_tx_en             <= 1'b0;
         o_rx_en             <= 1'b0;
         o_i3cengine_done    <= 1'b0;
         o_tx_mode           <= 3'b0;
         o_rx_mode           <= 3'b0;
         o_regf_addr         <= 10'b0;
         o_bit_cnt_en        <= 1'b0;
        
        case(state)
           IDLE:         
             begin
               if (i_i3cengine_en)
                   begin
                     state         <= BROADCAST;
                     o_rx_en       <= 1'b1;   // rx block enable
                     o_rx_mode     <= 3'b010; // arbitration state   
                     
                     o_regf_rd_en  <= 1'b1;
                     o_regf_addr   <= 10'b0000101110; // 9'd46 >> broadcast address in reg file ('h7E+w)
                     o_tx_en       <= 1'b1;
                     o_tx_mode     <= 3'b001;         // serializing state in TX
                     o_bit_cnt_en  <= 1'b1;
                   end
               else 
                   begin
 
                     state         <= IDLE;
                   end
               end
 
             
 
 
           BROADCAST:  
            begin
             
             if (i_tx_mode_done && i_scl_neg_edge )  // ****(scl neg edge condition check)
               begin
                state      <= ACK;
                o_rx_en    <= 1'b1;
                o_tx_en    <= 1'b0;
                o_rx_mode  <= 3'b000;  // ACK mode in rx   
                o_bit_cnt_en  <= 1'b0;
               end
             else 
               begin
                 state <= BROADCAST; 
                 o_rx_en       <= 1'b1;   // rx block enable
                 o_rx_mode     <= 3'b010; // arbitration state   
                 
                 o_regf_rd_en  <= 1'b1;
                 o_regf_addr   <= 10'b0000101110; // 9'd46 >> broadcast address in reg file ('h7E+w)
                 o_tx_en       <= 1'b1;
                 o_tx_mode     <= 3'b001;         // serializing state in TX
                 o_bit_cnt_en  <= 1'b1;
               end
            end
 
 
           ACK:         
            begin
 
             if(!i_rx_ack_nack && i_scl_neg_edge && i_rx_mode_done ) //if ACK next state is ENTHDR_DDR
               begin
                 state               <= ENTHDR_DDR;
                 o_regf_rd_en        <= 1'b1;  
                 o_regf_addr         <= 'd50;  //*** DDR Mode value added in the regfile but needs to be rechecked  
                 o_tx_mode           <= 3'b001;
                 o_tx_en             <= 1'b1;
                  o_bit_cnt_en       <= 1'b1;                
               end
             else 
               begin
                 state <= ACK;    //*** check: if not ack is received, what should be done?
                 o_rx_en    <= 1'b1;
                 o_tx_en    <= 1'b0;
                 o_rx_mode  <= 3'b000;  // ACK mode in rx   
                 o_bit_cnt_en  <= 1'b0;
               end
             end
 
 
           ENTHDR_DDR: 
            begin
             if(i_tx_mode_done && i_scl_neg_edge)     // ****(scl neg edge condition check)
               begin
                 state         <= PARITY;  // next state is parity to send the T bit
                 o_tx_en       <= 1'b1;
                 o_tx_mode     <= 3'b011;
                 o_bit_cnt_en  <= 1'b1;
               end
             else
               begin
                 state               <= ENTHDR_DDR;
                 o_regf_rd_en        <= 1'b1;  
                 o_regf_addr         <= 'd50;  //*** DDR Mode value added in the regfile but needs to be rechecked  
                 o_tx_mode           <= 3'b001;
                 o_tx_en             <= 1'b1;
                 o_bit_cnt_en        <= 1'b1; 
               end
             end
 
 
           PARITY:     
            begin
              if(i_tx_mode_done && i_scl_neg_edge )    ///*** T bit completion plus scl falling edge condition should be added
               begin
                 o_i3cengine_done <= 1'b1;
                 state            <= IDLE;
                 o_bit_cnt_en     <= 1'b0;
                 o_tx_en          <= 1'b0;
               end
              else
               begin
                 o_i3cengine_done <= 1'b0;
                 state            <= PARITY;
                 o_bit_cnt_en     <= 1'b1;
                 o_tx_en          <= 1'b1;
                 o_tx_mode        <= 3'b011;
               
               end
             end

           default:
            begin
             o_regf_rd_en        <= 1'b0;
             o_tx_en             <= 1'b0;
             o_rx_en             <= 1'b0;
             o_i3cengine_done    <= 1'b0;
             o_tx_mode           <= 3'b0;
             o_rx_mode           <= 3'b0;
             o_regf_addr         <= 10'b0;
             state               <= IDLE;
            end
         endcase
       end
   
 
   end
 
 endmodule

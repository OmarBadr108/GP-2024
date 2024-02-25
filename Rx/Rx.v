/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: 
 
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

module RX (

input                     i_sys_clk,
input                     i_sys_rst,
input                     i_sclgen_scl,
input                     i_sclgen_scl_pos_edge,
input                     i_sclgen_scl_neg_edge,
input                     i_ddrccc_rx_en,
input                     i_sdahnd_rx_sda,
input     [4:0]           i_bitcnt_rx_bit_count,
input     [2:0]           i_ddrccc_rx_mode,
input                     i_crc_value,
input                     i_crc_valid,

output  reg  [7:0]        o_regfcrc_rx_data_out,
output  reg               o_ddrccc_rx_mode_done,
output  reg               o_ddrccc_pre,
output  reg               o_ddrccc_error,
output  reg               o_crc_en                 

);
wire des_edge; 
assign des_edge = i_sclgen_scl_pos_edge || i_sclgen_scl_neg_edge;
/////////////////////////////////rx modes/////////////////////////////////


localparam [3:0]     
                    
                     FIRST_PREAMBLE      = 4'b0000  , 
                     SECOND_PREAMBLE     = 4'b0001  ,        
                     DESERIALIZING_BYTE  = 4'b0011  ,                   
                     CHECK_TOKEN         = 4'b0101  ,
                     CHECK_PAR_VALUE     = 4'b0110  ,
                     CHECK_CRC_VALUE     = 4'b0111  ,
                     ERROR               = 4'b1000  ;

always @(posedge i_sys_clk or negedge i_sys_rst) begin
  if (!i_sys_rst) begin

    o_regfcrc_rx_data_out <= 8'd0;  
    o_ddrccc_rx_mode_done <= 1'b0;
    o_ddrccc_pre          <= 1'b0;
    o_ddrccc_error        <= 1'b0;
    o_crc_en              <= 1'b0;   
    
  end

  else if (i_ddrccc_rx_en) begin

  case(i_ddrccc_rx_mode) 

    FIRST_PREAMBLE :begin
                     if (des_edge)
                      begin
                       o_ddrccc_pre <= i_sdahnd_rx_sda;
                       o_ddrccc_rx_mode_done <= 1'b1;
                      end
                      
 
                      else 
                       begin
                        o_ddrccc_rx_mode_done <= 1'b0;
                       end
                    end
 
    SECOND_PREAMBLE :begin
                     if (des_edge)
                      begin
                       o_ddrccc_pre <= i_sdahnd_rx_sda;
                       o_ddrccc_rx_mode_done <= 1'b1;
                      end
                      
 
                      else 
                       begin
                        o_ddrccc_rx_mode_done <= 1'b0;
                       end
                    end
 
 
 
    DESERIALIZING_BYTE :
 
    CHECK_TOKEN :   
 
    CHECK_PAR_VALUE : 
 
 
    CHECK_CRC_VALUE :
 
 
 
    ERROR :            


   
   endcase
end







endmodule
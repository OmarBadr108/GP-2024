/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Fatma Saad Abdallah
 
 Revision:   

 Version : 1.0

 Create Date: 19/2/2024
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


module crc_variable_input (
    input wire i_sys_clk,
    input wire i_sys_rst,
    input wire [7:0] i_parallel_data,
    input wire i_input_valid, //which is connected to mode done of tx
    input wire i_enable,
    output reg [4:0] o_crc_value,
    output reg o_crc_valid,
);

// CRC polynomial
parameter polynomial = 5'b101101; // 5-bit CRC polynomial
localparam  IDLE     = 1'b0,
            CALC_CRC = 1'b1;



// CRC registers
//reg [4:0] crc_reg;
reg [7:0] data_reg;
reg current_state, next_state;

 always@(posedge i_sys_clk or negedge i_sys_rst) begin
      if (!i_sys_rst) begin
        o_crc_value   <= 5'b00000; // Initialize CRC register to 0
        data_reg      <= 8'b0; // Initialize data register to 0
        o_crc_valid   <= 1'b0; // Output valid signal low on reset
        current_state <= IDLE;
      end
      else if (enable)
      begin
        current_state <= next_state;
        case (current_state)
                IDLE : begin 
                  //if(i_enable)
                    if(i_input_valid) begin
                      data_reg <= i_parallel_data;
                      o_crc_value <= 5'b00000;
                      o_crc_valid <= 1'b0;
                      next_state <= CALC_CRC;
                    end
                    else
                      begin
                      o_crc_value <= 5'b00000;
                      o_crc_valid <= 1'b0;
                      next_state <= IDLE;
                      end
                end

                CALC_CRC : begin
                    ///calc crc

                  if(i_input_valid) //mfrud aCheck an valid atrf3 tany w ana 5lst al 8 bits aly ablhum
                    next_state <= IDLE;
                  else
                    begin
                      o_crc_valid <= 1'b1;
                      //o_crc_value <= 5'b;
                    end

                end
        endcase
      end
      else
      begin
        o_crc_value <= 5'b00000;
        o_crc_valid <= 1'b0;
      end
end

          







/*
// CRC calculation process
always @(posedge i_sys_clk or negedge i_sys_rst) begin
    if (reset) begin
        crc_reg <= 5'b00000; // Initialize CRC register to 0
        data_reg <= 8'b0; // Initialize data register to 0
        crc_valid <= 1'b0; // Output valid signal low on reset
    end else if (enable) begin
        if (input_valid) begin
            // Shift CRC register left by one bit
            crc_reg <= {crc_reg[3:0], crc_reg[4]};
            // Load incoming data into data register
            data_reg <= i_parallel_data;
            // XOR the MSB of CRC with incoming data
            crc_reg[4] <= crc_reg[4] ^ data_reg[7];

        end
        else
          crc_reg <= 5'b0;
    end
    else
    crc_reg <= 5'b0;
end
*/
endmodule


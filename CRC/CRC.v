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
reg [2:0] counter;  // Counter to keep track of bit position
reg serial_out;
 always@(posedge i_sys_clk or negedge i_sys_rst) begin
      if (!i_sys_rst) begin
        o_crc_value   <= 5'b00000; // Initialize CRC register to 0
        data_reg      <= 8'b0; // Initialize data register to 0
        o_crc_valid   <= 1'b0; // Output valid signal low on reset
        current_state <= IDLE;
        counter <= 3'b000;
      end
      else if (enable)
      begin
        current_state <= next_state;
        case (current_state)
                IDLE : begin 
                  //if(i_enable)
                    if(i_input_valid) begin
                      data_reg <= i_parallel_data;
                      if (counter < 3'b111)
                        counter <= counter + 1;
                      else
                        counter <= 3'b000;

                        // Output serial_out based on the counter value
                        case(counter)
                          3'b000: serial_out <= data_reg[0];
                          3'b001: serial_out <= data_reg[1];
                          3'b010: serial_out <= data_reg[2];
                          3'b011: serial_out <= data_reg[3];
                          3'b100: serial_out <= data_reg[4];
                          3'b101: serial_out <= data_reg[5];
                          3'b110: serial_out <= data_reg[6];
                          3'b111: serial_out <= data_reg[7];
                          default: serial_out <= 1'b0; // Default case
                        endcase
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


/*

module serializer(
    input clk,       // Clock input
    input reset,     // Reset input
    input [7:0] data_in, // 8-bit input data
    output reg serial_out // Serialized output
);

reg [2:0] counter;  // Counter to keep track of bit position

always @(posedge clk or posedge reset) begin
    if (reset) begin
        counter <= 3'b000; // Reset counter
        serial_out <= 1'b0; // Reset serial output
    end else begin
        // Shift data_out left on every clock cycle
        if (counter < 3'b111)
            counter <= counter + 1;
        else
            counter <= 3'b000;

        // Output serial_out based on the counter value
        case(counter)
            3'b000: serial_out <= data_in[0];
            3'b001: serial_out <= data_in[1];
            3'b010: serial_out <= data_in[2];
            3'b011: serial_out <= data_in[3];
            3'b100: serial_out <= data_in[4];
            3'b101: serial_out <= data_in[5];
            3'b110: serial_out <= data_in[6];
            3'b111: serial_out <= data_in[7];
            default: serial_out <= 1'b0; // Default case
        endcase
    end
end

endmodule
*/
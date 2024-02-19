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
    input wire [7:0] i_data_in,
    input wire input_valid,
    input wire input_last,
    input wire enable,
    output reg [4:0] crc_value,
    output reg crc_valid,
    output reg output_last
);

// CRC polynomial
parameter polynomial = 5'b101101; // 5-bit CRC polynomial

// CRC registers
reg [4:0] crc_reg;
reg [7:0] data_reg;

// CRC calculation process
always @(posedge i_sys_clk or posedge i_sys_rst) begin
    if (reset) begin
        crc_reg <= 5'b00000; // Initialize CRC register to 0
        data_reg <= 8'b0; // Initialize data register to 0
        crc_valid <= 1'b0; // Output valid signal low on reset
        output_last <= 1'b0; // Output last signal low on reset
    end else if (enable) begin
        if (input_valid) begin
            // Shift CRC register left by one bit
            crc_reg <= {crc_reg[3:0], crc_reg[4]};
            // XOR the MSB of CRC with incoming data
            crc_reg[4] <= crc_reg[4] ^ data_reg[7];
            // Load incoming data into data register
            data_reg <= i_parallel_data;
            // If last byte of input, set output_last
            if (input_last) begin
                output_last <= 1'b1;
            end
        end
    end
end

// Output CRC when input is valid and last byte received
always @(*) begin
    if (input_valid && input_last) begin
        crc_value = crc_reg;
        crc_valid = 1'b1;
    end else begin
        crc_value = 5'b0;
        crc_valid = 1'b0;
    end
end

endmodule
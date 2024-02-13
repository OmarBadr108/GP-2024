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

module CCC_Handler #(



) (
input wire        i_sys_clk ,
input wire        i_sys_rst ,
input wire        i_engine_en ,
input wire        i_frmcnt_last ,
input wire [4:0]  i_bitcnt_number ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire        i_rx_second_pre ,
input wire        i_sclgen_neg_edge ,
input wire        i_sclgen_pos_edge ,
input wire        i_sclstall_stall_done ,
input wire        i_regf_wr_rd_bit ,
input wire        I_rx_error ,

output reg        o_sclstall_en ,
output reg [7:0]  o_sclstall_no_of_cycles ,
output reg        o_tx_en ,
output reg [3:0]  o_tx_mode ,
output reg        o_rx_en ,
output reg [2:0]  o_rx_mode ,
output reg        o_bitcnt_en ,
output reg        o_bitcnt_err_rst ,
output reg        o_frmcnt_en ,
output reg        o_sdahand_pp_od ,
output reg        o_regf_wr_en ,
output reg        o_regf_rd_en ,
output reg [7:0]  o_regf_addr ,
output reg        o_engine_done ,
output reg        o_engine_semi_done 

);


reg [4:0]         current_state , next_state ;




// localparam to prevent overriding the states from outside the design
// as states encoding should never be modified from outside (while instatiation)
// after revision i will convert the coding style to grey
localparam IDLE               = 5'd00000 ;
localparam PRE_FIRST_CMD_CRC  = 5'd00001 ;
localparam RNW_RESERVED       = 5'd00010 ;
localparam SEVEN_E            = 5'd00011 ;

localparam PARITY_ADJ         = 5'd00100 ;
localparam PARITY_ADJ         = 5'd00101 ;
localparam FIRST_DATA_BYTE    = 5'd00110 ;
localparam SECOND_DATA_BYTE   = 5'd00111 ;

localparam PRE_FIRST_DATA     = 5'd01000 ;
localparam PRE_DATA           = 5'd01001 ;
localparam CRC                = 5'd01010 ;
localparam HDR_RESTART_PATTER = 5'd01011 ;


// state memory (sequential)
    always @(posedge i_sys_clk or negedge i_sys_rst) begin
        if (!i_sys_rst) begin
            current_state <= IDLE ;
        end
        else  begin
            current_state <= next_state ;
        end
    end
// output logic and next state logic (pure combinational logic)
    always@(*)begin
        case (current_state)

            IDLE : begin  // aw arbitration if needed  


            end 

            PRE_FIRST_CMD_CRC : begin // i'm driving the 2 bits with 2'b01

                
            end 

            RNW_RESERVED : begin 

                
            end

            SEVEN_E : begin 

                
            end

            PARITY_ADJ : begin 

                
            end

            PARITY : begin 

                
            end







            FIRST_DATA_BYTE : begin    // contains CCC value or First Data byte

                
            end

            SECOND_DATA_BYTE : begin   // contains Optional Defining Byte (8'd0 if none is used) , or second data byte

                
            end

            PRE_FIRST_DATA : begin  // should be 10 to mean ACK and 11 to be aborted 

                
            end

            PRE_DATA : begin        // should be 11 to mean ACK and 10 to be aborted 

                
            end






            CRC : begin // this state can handle the rest of the CRC word 

                
            end

            HDR_RESTART_PATTER : begin 

            end 




        endcase
    end
endmodule 
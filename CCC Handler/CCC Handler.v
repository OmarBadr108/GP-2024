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
input wire        i_engine_en ,                 // depends on CP flag 
input wire [4:0]  i_bitcnt_number ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire        i_rx_second_pre ,
input wire        i_sclgen_neg_edge ,
input wire        i_sclgen_pos_edge ,
input wire        i_sclstall_stall_done ,
input wire        i_rx_error , // sus 

// configuration Ports coming from regf
input wire        i_regf_RnW ,
input wire [2:0]  i_regf_CMD_ATTR ,
input wire [7:0]  i_regf_CMD ,
input wire [4:0]  i_regf_DEV_INDEX ,
input wire        i_regf_TOC , 
input wire        i_regf_WROC , 

// in case of immidiate command descriptor 
input wire [2:0]  i_regf_DTT , 

// in case of regular command descriptor 
input wire        i_regf_DBP , 
input wire        i_regf_SRE , 
input wire [15:0] i_regf_DATA_LENGTH ,



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

reg               Direct_Broadcast_n ;               // 1 for direct and 0 for broadcast
reg               Direct_Broadcast_n_internal ;      // sampled version of the above signal every CCC transmission (sampled at first command state)

/////////////////////////// Direct or Broadcat detection  ////////////////////////////////////////

// we have 13 required CCC to support at ground level 
// to determine whether it's a Direct or Broadcast 
    always @(*) begin 
        case (i_config_CCC_value) 
            8'h80 : Direct_Broadcast_n = 1'b1 ;   // ENEC
            8'h81 : Direct_Broadcast_n = 1'b1 ;   // DISEC
            8'h89 : Direct_Broadcast_n = 1'b1 ;   // SETMWL
            8'h8A : Direct_Broadcast_n = 1'b1 ;   // SETMRL
            8'h8B : Direct_Broadcast_n = 1'b1 ;   // GETMWL
            8'h8C : Direct_Broadcast_n = 1'b1 ;   // GETMRL
            8'h9A : Direct_Broadcast_n = 1'b1 ;   // RSTACT
            8'h90 : Direct_Broadcast_n = 1'b1 ;   // GETSTATUS

            8'h00 : Direct_Broadcast_n = 1'b0 ;   // ENEC   (broadcast version)
            8'h01 : Direct_Broadcast_n = 1'b0 ;   // DISEC  (broadcast version)
            8'h09 : Direct_Broadcast_n = 1'b0 ;   // SETMWL (broadcast version)
            8'h0A : Direct_Broadcast_n = 1'b0 ;   // SETMRL (broadcast version)
            8'h2A : Direct_Broadcast_n = 1'b0 ;   // RSTACT (broadcast version)

            8'h1F : Direct_Broadcast_n = 1'b0 ;    // Dummy CCC value for end procedure
            default : Direct_Broadcast_n = 1'b0 ;  // broadcast by default
        endcase
    end


///////////////////////////////// state encoding //////////////////////////////////////////////

// localparam to prevent overriding the states from outside the design
// as states encoding should never be modified from outside (while instatiation)
// after revision i will convert the coding style to grey
localparam IDLE              = 5'd00000 ;
localparam PRE_FIRST_CMD_CRC = 5'd00001 ;
localparam RNW_RESERVED      = 5'd00010 ;
localparam SEVEN_E           = 5'd00011 ;

localparam PARITY_ADJ        = 5'd00100 ;
localparam PARITY_ADJ        = 5'd00101 ;
localparam FIRST_DATA_BYTE   = 5'd00110 ;
localparam SECOND_DATA_BYTE  = 5'd00111 ;

localparam PRE_FIRST_DATA    = 5'd01000 ;
localparam PRE_DATA          = 5'd01001 ;
localparam CRC               = 5'd01010 ;
localparam RESTART_PATTERN   = 5'd01011 ;
localparam ERROR             = 5'd01100 ;



wire            Defining_byte ; 

// Defining Byte identification 
always @(*) begin 
    if      (!i_regf_CMD_ATTR[0] && i_regf_DBP)       Defining_byte = 1'b1 ; // regular 
    else if (i_regf_CMD_ATTR[0] && i_regf_DTT[2])     Defining_byte = 1'b1 ; // immediate
    else                                              Defining_byte = 1'b0 ;

end 
///////////////////////////////// state memory //////////////////////////////////////////////
    always @(posedge i_sys_clk or negedge i_sys_rst) begin
        if (!i_sys_rst) begin
            current_state <= IDLE ;
        end
        else  begin
            current_state <= next_state ;
        end
    end

///////////////////////////////// next state and output logic //////////////////////////////////////////////
    always@(*)begin
        case (current_state)

            IDLE : begin  // aw arbitration if needed  

                if (i_engine_en) begin 
                    next_state = PRE_FIRST_CMD_CRC ;
                end
                else begin 
                    next_state = IDLE ;
                end 

                 // erorr state condition is remaining  

            end 

            PRE_FIRST_CMD_CRC : begin // i'm driving the 2 bits with 2'b01

                if (i_bitcnt_number == 5'd2 && i_tx_mode_done) begin 
                    next_state = FIRST_CMD_BYTE ;
                end 
                else begin 
                    next_state = PRE_FIRST_CMD_CRC ;
                end

                 // erorr state condition is remaining 

            end 

            FIRST_CMD_BYTE : begin  //  always contains RnW + 7 reserved bits 

                Direct_Broadcast_n_internal = Direct_Broadcast_n ; 

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done) begin 
                    next_state = SECOND_CMD_BYTE ;
                end
                else begin 
                    next_state = FIRST_CMD_BYTE ;
                end

                 // erorr state condition is remaining 

            end

            SECOND_CMD_BYTE : begin  // contains either 7E or any target address 
                if (Direct_Broadcast_n_internal) begin 
                    // tx mode on 7E value
                    if (i_bitcnt_number == 5'd17 && i_tx_mode_done) begin 
                        next_state = PARITY_ADJ ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end
                    
                     // erorr state condition is remaining 
                end 
                else begin 
                    // tx mode on target address 
                    if (i_bitcnt_number == 5'd17 && i_tx_mode_done) begin 
                        next_state = PARITY_ADJ ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end
                    
                     // erorr state condition is remaining
                end 
            end

            PARITY_ADJ : begin 

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin 
                    next_state = PARITY_CMD ;
                end
                else begin 
                    next_state = PARITY_ADJ ;
                end

                 // erorr state condition is remaining 

            end

            PARITY_CMD : begin 

                if (i_bitcnt_number == 5'd20 && i_tx_mode_done ) begin 
                    next_state = PRE_FIRST_DATA ;
                end
                else begin 
                    next_state = PARITY_CMD ;
                end

                // erorr state condition is remaining 

            end



            PRE_FIRST_DATA : begin  // should be 10 to mean ACK ,    and 11 to be aborted 
                // tx mode on 1 
                // enable rx and check the target's response
                if (i_bitcnt_number == 5'd2 && i_rx_mode_done && !i_rx_second_pre) begin 
                    next_state = CCC_BYTE ;
                end
                else if (i_bitcnt_number == 5'd2 && i_rx_mode_done && i_rx_second_pre) begin 
                    next_state = ERROR ;
                end
                else begin
                    next_state = PRE_FIRST_DATA ;
                end
            end


            CCC_BYTE : begin    // contains CCC value

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done && Defining_byte) begin   // if a defining byte exists
                    next_state = DEFINING_BYTE ;
                end
                else if (i_bitcnt_number == 5'd10 && i_tx_mode_done && !Defining_byte) begin   
                    next_state = FIRST_DATA_BYTE ;
                end
                else begin 
                    next_state = CCC_BYTE ;
                end

                // erorr state condition is remaining 

                
            end


            DEFINING_BYTE : begin    // contains definaing byte if exist

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_CCC_DEF ;
                end
                else begin 
                    next_state = DEFINING_BYTE ;
                end

                // erorr state condition is remaining 

                
            end

            PARITY_CCC_DEF : begin // parity state for CCC and Def byte

                if  (i_bitcnt_number == 5'd20 && i_tx_mode_done && !Direct_Broadcast_n_internal ) begin // if broadcast
                    next_state = PRE_DATA ;
                end

                else if (i_bitcnt_number == 5'd20 && i_tx_mode_done &&  Direct_Broadcast_n_internal ) begin // if Direct
                    next_state = RESTART_PATTERN ;
                    Direct_Broadcast_n_internal = 1'b0 ; // resetting the signal after sending broadcast address to transmitt target address in the next command word 
                end

                else begin 
                    next_state = PARITY_CCC_DEF ;
                end

                // erorr state condition is remaining 

            end

            PARITY_DATA : begin // parity state for repeated data (not CCC and Def byte)

                if  (i_bitcnt_number == 5'd20 && i_tx_mode_done && last_byte) begin 
                    next_state = CRC ;
                end

                else if (i_bitcnt_number == 5'd20 && i_tx_mode_done && !last_byte) begin 
                    next_state = PRE_DATA ;
                end

                else begin 
                    next_state = PARITY_DATA ;
                end

                // erorr state condition is remaining 

            end



            PRE_DATA : begin        // should be 11 to mean ACK and 10 to be aborted 
                // tx mode on 1 
                // enable rx and check the target's response
                if (i_bitcnt_number == 5'd2 && i_rx_mode_done && i_rx_second_pre) begin 
                    next_state = FIRST_DATA_BYTE ;
                end
                else if (i_bitcnt_number == 5'd2 && i_rx_mode_done && !i_rx_second_pre) begin 
                    next_state = ERROR ;
                end
                else begin
                    next_state = PRE_DATA ;
                end
                
            end


            FIRST_DATA_BYTE : begin    // contains first repeated data byte

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done) begin  
                    next_state = SECOND_DATA_BYTE ;
                end
                else begin 
                    next_state = FIRST_DATA_BYTE ;
                end

                // erorr state condition is remaining 
     
            end


            SECOND_DATA_BYTE : begin   // contains second repeated data byte

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = SECOND_DATA_BYTE ;
                end

                // erorr state condition is remaining
                
            end

           
           


















            CRC : begin // this state can handle the rest of the CRC word 

                
            end

            RESTART_PATTERN : begin 

            end 

            ERROR : begin 

            end 



        endcase
    end
endmodule 


// remmeber to handle last frame logic and the case that the payload is odd number of bytes
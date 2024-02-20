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



output reg        o_sclstall_en      ,
output reg [7:0]  o_sclstall_code    ,
output reg        o_tx_en            ,
output reg [3:0]  o_tx_mode          ,
output reg        o_rx_en            ,
output reg [2:0]  o_rx_mode          ,
output reg        o_bitcnt_en        ,
output reg        o_bitcnt_err_rst   ,
output reg        o_frmcnt_en        ,
output reg        o_sdahand_pp_od    ,
output reg        o_regf_wr_en       ,
output reg        o_regf_rd_en       ,
output reg [7:0]  o_regf_addr        ,
output reg        o_engine_done      


);



// internal signals 
reg [4:0]         current_state , next_state ;
reg               Direct_Broadcast_n ;               // 1 for direct and 0 for broadcast
reg               Direct_Broadcast_n_internal ;      // sampled version of the above signal every CCC transmission (sampled at first command state)
reg [6:0]         target_addres ;
wire              Defining_byte ; 
wire              first_time ;




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

// tx modes parameters 
localparam [3:0]  
                zero                = 4'd0  ,  // 0 
                one                 = 4'd1  ,  // 1 
                special_preamble    = 4'd2  ,  // 01 of cmd word 
                seven_zeros         = 4'd3  ,  // 7'b 0000_000
                seven_e             = 4'd4  ,  // 7'b 111_1110
                serializing_address = 4'd5  ,  // serializing 7 bits 
                serializing_byte    = 4'd6  ,  // serializing 8 bits 
                parity_adj          = 4'd7  ,
                parity_calc         = 4'd8  ,
                
                token_CRC           = 4'd10 ,  // 4'hC
                restart_pattern     = 4'd11 , 
                exit_pattern        = 4'd12 ;

// regile parameters 
localparam [:0] first_data_byte_address = ;
localparam [:0] ccc_value_address = ;


// rx parameters 
localparam second_preamble_rx = 3'd0 ;




/////////////////////////// decoding the device address (DAT entry 3al daya2 :) )///////////////////////////////////////

always@(*) begin
    case (i_regf_DEV_INDEX)                     // 32 possible targets can present on bus
        5'd0 : target_addres = 7'd8  ;
        5'd0 : target_addres = 7'd9  ;
        5'd0 : target_addres = 7'd10 ;
        5'd0 : target_addres = 7'd11 ;

        5'd0 : target_addres = 7'd12 ;
        5'd0 : target_addres = 7'd13 ;
        5'd0 : target_addres = 7'd14 ;
        5'd0 : target_addres = 7'd15 ;

        5'd0 : target_addres = 7'd16 ;
        5'd0 : target_addres = 7'd17 ;
        5'd0 : target_addres = 7'd18 ;
        5'd0 : target_addres = 7'd19 ;

        5'd0 : target_addres = 7'd20 ;
        5'd0 : target_addres = 7'd21 ;
        5'd0 : target_addres = 7'd22 ;
        5'd0 : target_addres = 7'd23 ;

        5'd0 : target_addres = 7'd24 ;
        5'd0 : target_addres = 7'd25 ;
        5'd0 : target_addres = 7'd26 ;
        5'd0 : target_addres = 7'd27 ;

        5'd0 : target_addres = 7'd28 ;
        5'd0 : target_addres = 7'd29 ;
        5'd0 : target_addres = 7'd30 ;
        5'd0 : target_addres = 7'd31 ;

        5'd0 : target_addres = 7'd32 ;
        5'd0 : target_addres = 7'd33 ;
        5'd0 : target_addres = 7'd34 ;
        5'd0 : target_addres = 7'd35 ;

        5'd0 : target_addres = 7'd36 ;
        5'd0 : target_addres = 7'd37 ;
        5'd0 : target_addres = 7'd38 ;
        5'd0 : target_addres = 7'd39 ;
    endcase
end  

/////////////////////////// Direct or Broadcat detection  ////////////////////////////////////////

// we have 13 required CCC to support at ground level 
// to determine whether it's a Direct or Broadcast 
    always @(*) begin 
        case (i_regf_CMD) 
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

 
// Defining Byte identification 
always @(*) begin 
    if      (!i_regf_CMD_ATTR[0] && i_regf_DBP)                                                      Defining_byte = 1'b1 ; // regular 
    else if (i_regf_CMD_ATTR[0] && ( i_regf_DTT == 3'd5 |  i_regf_DTT == 3'd6 | i_regf_DTT == 3'd7)  Defining_byte = 1'b1 ; // immediate      
    else                                                                                             Defining_byte = 1'b0 ;

end 
//////////////////////////////////////////// state memory /////////////////////////////////////////////////
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

    // initial values of outputs 

    o_sclstall_en      = 1'b0 ;  
    o_sclstall_code    = 8'b0 ; 
    o_tx_en            = 1'b0 ; 
    o_tx_mode          = 4'b0 ; 
    o_rx_en            = 1'b0 ; 
    o_rx_mode          = 3'b0 ; 
    o_bitcnt_en        = 1'b1 ; // enabled in all states except for idle state
    o_bitcnt_err_rst   = 1'b0 ; 
    o_frmcnt_en        = 1'b0 ; 
    o_sdahand_pp_od    = 1'b1 ; // 1 means PP
    o_regf_wr_en       = 1'b0 ;
    o_regf_rd_en       = 1'b0 ;
    o_regf_addr        = 8'b0 ;
    o_engine_done      = 1'b0 ;


        case (current_state)

            IDLE : begin                                        // aw arbitration if needed  
                first_time  = 1'b1 ;                             // flag to help to differentiate between the direct and broadcast with assistance of Direct_Braodcast_n flag 
                o_bitcnt_en = 1'b0 ;

                if (i_engine_en) begin 
                    next_state = PRE_CMD ;
                end
                else begin 
                    next_state = IDLE ;
                end 

                // erorr state condition is remaining  
            end 

            PRE_CMD : begin // i'm driving the 2 bits with 2'b01

                o_tx_en   = 1'b1 ; 
                o_tx_mode = special_preamble ; 

                if (i_bitcnt_number == 5'd2 && i_tx_mode_done) begin 
                    next_state = FIRST_CMD_BYTE ;
                end 
                else begin 
                    next_state = PRE_CMD ;
                end

                 // erorr state condition is remaining 

            end 

            FIRST_CMD_BYTE : begin  //  always contains RnW + 7 reserved bits 
                o_tx_en   = 1'b1 ;
                if (first_time) begin  
                    o_tx_mode = zero ;                                      // always RnW field is 0 with broadcast address
                    if ((i_bitcnt_number == 3) && i_tx_mode_done) begin 
                       o_tx_mode = seven_zeros ; 
                    end 
                end 
                else begin 
                     
                    if (i_regf_RnW) o_tx_mode = one  ; // read 
                    else            o_tx_mode = zero  ; // write 

                    if ((i_bitcnt_number == 3) && i_tx_mode_done) begin 
                       o_tx_mode = seven_zeros ; 
                    end 
                end 

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done) begin 
                    next_state = SECOND_CMD_BYTE ;
                    
                end
                else begin 
                    next_state = FIRST_CMD_BYTE ;
                end

                 // erorr state condition is remaining 

            end

            SECOND_CMD_BYTE : begin  // contains either 7E or any target address 
                o_tx_en   = 1'b1 ; 
                if (Direct_Broadcast_n && first_time) begin 

                    o_tx_mode = seven_E ;

                    if (i_bitcnt_number == 5'd17 && i_tx_mode_done) begin 
                        next_state = PARITY_ADJ ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end
                    
                     // erorr state condition is remaining 
                end 
                else begin 
                    o_regf_addr  =  ;                              /////////////// this is a fixed location in the regfile 
                    o_regf_rd_en = 1'b1 ;
                    o_tx_mode    = Serializing_address ;

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
                o_tx_en   = 1'b1 ; 
                o_tx_mode = parity_adj ;

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin 
                    next_state = PARITY_CMD ;
                end
                else begin 
                    next_state = PARITY_ADJ ;
                end

                 // erorr state condition is remaining 

            end

            PARITY_CMD : begin 
                o_tx_en   = 1'b1 ; 
                o_tx_mode = parity_calc ;

                if (i_bitcnt_number == 5'd20 && i_tx_mode_done) begin 
                    next_state = PRE_FIRST_DATA ;
                end
                else begin 
                    next_state = PARITY_CMD ;
                end

                // erorr state condition is remaining 

            end



            PRE_FIRST_DATA : begin  // should be 10 to mean ACK ,    and 11 is NACK
                
                if (i_bitcnt_number == 5'd1 && i_tx_mode_done) begin 
                    o_tx_en   = 1'b0 ;
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = second_preamble_rx ;
                end 
                else begin 
                    o_tx_en   = 1'b1 ; 
                    o_tx_mode = one ;
                end 
                // enable rx and check the target's response
                if (i_bitcnt_number == 5'd2 && i_rx_mode_done && !i_rx_second_pre) begin 
                    next_state = CCC_BYTE ;
                    //o_tx_en    = 1'b1 ;
                    //o_rx_en    = 1'b0 ;
                end
                else if (i_bitcnt_number == 5'd2 && i_rx_mode_done && i_rx_second_pre) begin 
                    next_state = ERROR ;
                end
                else begin
                    next_state = PRE_FIRST_DATA ;
                end
            end


            CCC_BYTE : begin    // contains CCC value

                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte ;
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = ccc_value_address ;

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done && Defining_byte) begin   // if a defining byte exists
                    next_state = DEFINING_BYTE ;
                end
                else if (i_bitcnt_number == 5'd10 && i_tx_mode_done && !Defining_byte) begin   
                    next_state = ZEROS ; 
                end
                else begin 
                    next_state = CCC_BYTE ;
                end

                // erorr state condition is remaining 

                
            end


            DEFINING_BYTE : begin    // contains definaing byte if exist
                o_tx_en   = 1'b1 ;
                o_tx_mode = serializing_byte ; 

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = DEFINING_BYTE ;
                end

                // erorr state condition is remaining 

                
            end
/*
            ZEROS : begin    // transmit 8 zeros usen in case of absence of Def byte or odd number of data byte is requested

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = ZEROS ;
                end

                // erorr state condition is remaining 

                
            end
*/
            PARITY_DATA : begin // parity state any Data word

                if  (i_bitcnt_number == 5'd20 && i_tx_mode_done) begin // if broadcast

                    if (last_byte || (Direct_Broadcast_n & first_time)) begin  // crc state only in case of Direct or in case of last data 
                        next_state = CRC ;
                    end 
                    else begin 
                        next_state = PRE_DATA ; // not last byte then continue sending repeated data 
                    end 
                end

                else begin 
                    next_state = PARITY_DATA ;
                end

                // erorr state condition is remaining 

            end


            PRE_DATA : begin        //  11  means ok continue , and 10 to be aborted 
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


            CRC : begin // this state can handle the rest of the CRC word (2 + 4 + 5 + 1)
                first_time = 1'b0 ;
                if (i_bitcnt_number < 5'd2)
                // tx mode on preamble 01  

                if (i_bitcnt_number == 5'd2 && i_tx_mode_done) begin 
                   // tx mode on C token  
                end
                else if (i_bitcnt_number == 5'd6 && i_tx_mode_done) begin 
                    // tx mode on 5-bits CRC checksum 
                end 
                else if (i_bitcnt_number == 5'd11 && i_tx_mode_done) begin 
                    // tx mode is stalled at 1 (preparing for restart or exit pattern)
                end 
                else if (i_bitcnt_number == 5'd12 && i_tx_mode_done) begin 
                    // finish a command discriptor
                    o_engine_done = 1'b1 ;

                    if (i_regf_TOC) begin 
                        next_state = EXIT_PATTERN ;
                    end 
                    else begin 
                        next_state = RESTART_PATTERN ;
                    end
                end
                else begin 
                    next_state = CRC ;
                end 

                
            end

            RESTART_PATTERN : begin 
                // access timer and staller and tx to perform restart pattern 
                if (i_sclstall_stall_done && i_tx_mode_done) begin 
                    next_state = IDLE ;
                end  
                else begin 
                    next_state = RESTART_PATTERN ;
                end
            end 




            EXIT_PATTERN : begin 
                // access timer and staller and tx to perform exit pattern 
                if (i_sclstall_stall_done && i_tx_mode_done) begin 
                    next_state = IDLE ;
                end  
                else begin 
                    next_state = EXIT_PATTERN ;
                end
            end




            ERROR : begin 

            end 





        endcase
    end
endmodule 



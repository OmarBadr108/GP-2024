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

module CCC_Handler (
input wire        i_sys_clk ,
input wire        i_sys_rst ,
input wire        i_engine_en ,                 // depends on CP flag 
input wire [4:0]  i_bitcnt_number ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire        i_rx_second_pre ,
input wire        i_sclstall_stall_done ,
input wire        i_rx_error , // sus 
input wire        i_frmcnt_last_frame ,

// configuration Ports coming from regf
input wire        i_regf_RnW ,          
input wire [2:0]  i_regf_CMD_ATTR ,
input wire [7:0]  i_regf_CMD ,          // CCC value 
input wire [4:0]  i_regf_DEV_INDEX ,
input wire        i_regf_TOC , 
input wire        i_regf_WROC , 

// in case of immidiate command descriptor 
input wire [2:0]  i_regf_DTT , 

// in case of regular command descriptor 
input wire        i_regf_DBP , 
input wire        i_regf_SRE , 
input wire [15:0] i_regf_DATA_LENGTH , // will be removed 



output reg        o_sclstall_en      ,
output reg [7:0]  o_sclstall_code    ,
output reg        o_tx_en            ,
output reg [3:0]  o_tx_mode          ,
output reg        o_rx_en            ,
output reg [2:0]  o_rx_mode          ,
output reg        o_bitcnt_en        ,
output reg        o_bitcnt_err_rst   , // ???
output reg        o_frmcnt_en        ,
output reg        o_sdahand_pp_od    ,
output reg        o_regf_wr_en       ,
output reg        o_regf_rd_en       ,
output reg [7:0]  o_regf_addr        , // depends on the depth of the regfile
output reg        o_engine_done      ,
output reg [7:0]  o_txrx_addr_ccc    ,         // new 
output reg        o_engine_odd                 // new
);   



// internal signals 
reg [4:0] current_state , next_state ;
reg       Direct_Broadcast_n ;               // 1 for direct and 0 for broadcast
reg [6:0] target_addres ;
reg       Defining_byte ; 
reg       first_time ;
integer   regular_counter ;
integer   immediate_counter ; 



///////////////////////////////// state encoding //////////////////////////////////////////////

// localparam to prevent overriding the states from outside the design
// as states encoding should never be modified from outside (while instatiation)
// after revision i will convert the coding style to grey
localparam [4:0] IDLE             = 5'b00000 ;
localparam [4:0] PRE_CMD          = 5'b00001 ;
localparam [4:0] FIRST_CMD_BYTE   = 5'b00010 ;
localparam [4:0] SECOND_CMD_BYTE  = 5'b00011 ;

localparam [4:0] PARITY_CMD       = 5'b00100 ;
localparam [4:0] PRE_FIRST_DATA   = 5'b00101 ;
localparam [4:0] CCC_BYTE         = 5'b00110 ;
localparam [4:0] DEFINING_BYTE    = 5'b00111 ;

localparam [4:0] ZEROS            = 5'b01000 ;
localparam [4:0] PARITY_DATA      = 5'b01001 ;
localparam [4:0] PRE_DATA         = 5'b01010 ;
localparam [4:0] FIRST_DATA_BYTE  = 5'b01011 ;

localparam [4:0] SECOND_DATA_BYTE = 5'b01100 ;
localparam [4:0] CRC              = 5'b01101 ;
localparam [4:0] RESTART_PATTERN  = 5'b01110 ;
localparam [4:0] EXIT_PATTERN     = 5'b01111 ;

localparam [4:0] ERROR            = 5'b10000 ;




// tx modes parameters 
localparam [3:0]  
                zero                      = 4'd0  ,  // 0 
                one                       = 4'd1  ,  // 1 
                special_preamble          = 4'd2  ,  // 01 of cmd word 
                seven_zeros               = 4'd3  ,  // 7'b 0000_000
                seven_e                   = 4'd4  ,  // 7'b 111_1110
                serializing_address       = 4'd5  ,  // serializing 7 bits 
                serializing_byte          = 4'd6  ,  // serializing 8 bits 
                parity_calc               = 4'd7  ,
                c_token_CRC               = 4'd8 ,  // 4'hC
                value_CRC                 = 4'd9 ,  // 5 bit value
                restart_pattern           = 4'd10 , 
                exit_pattern              = 4'd11 ,
                serializing_sec_byte_only = 4'd12 ;


// regfile parameters 
localparam first_location = 'd1000 ;

// rx parameters 
localparam second_preamble_rx = 3'd0 ;

// SCL staller parameters 
localparam [3:0] restart_pattern_stall = 4'b1111 ;
localparam [3:0] exit_pattern_stall    = 4'b1110 ;
/////////////////////////// decoding the device address (DAT entry 3al daya2 :) ) ///////////////////////////////////////

always@(*) begin
    case (i_regf_DEV_INDEX)                     // 32 possible targets can present on bus
        5'd0 : target_addres = 7'd8  ;
        5'd1 : target_addres = 7'd9  ;
        5'd2 : target_addres = 7'd10 ;
        5'd3 : target_addres = 7'd11 ;

        5'd4 : target_addres = 7'd12 ;
        5'd5 : target_addres = 7'd13 ;
        5'd6 : target_addres = 7'd14 ;
        5'd7 : target_addres = 7'd15 ;

        5'd8 : target_addres = 7'd16 ;
        5'd9 : target_addres = 7'd17 ;
        5'd10: target_addres = 7'd18 ;
        5'd11: target_addres = 7'd19 ;

        5'd12: target_addres = 7'd20 ;
        5'd13: target_addres = 7'd21 ;
        5'd14: target_addres = 7'd22 ;
        5'd15: target_addres = 7'd23 ;

        5'd16: target_addres = 7'd24 ;
        5'd17: target_addres = 7'd25 ;
        5'd18: target_addres = 7'd26 ;
        5'd19: target_addres = 7'd27 ;

        5'd20: target_addres = 7'd28 ;
        5'd21: target_addres = 7'd29 ;
        5'd22: target_addres = 7'd30 ;
        5'd23: target_addres = 7'd31 ;

        5'd24: target_addres = 7'd32 ;
        5'd25: target_addres = 7'd33 ;
        5'd26: target_addres = 7'd34 ;
        5'd27: target_addres = 7'd35 ;

        5'd28: target_addres = 7'd36 ;
        5'd29: target_addres = 7'd37 ;
        5'd30: target_addres = 7'd38 ;
        5'd31: target_addres = 7'd39 ;
    endcase

end  

//////////////////////////////////////// Direct or Broadcat detection  ///////////////////////////////////////////////

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
        if      (!i_regf_CMD_ATTR[0] && i_regf_DBP)                                                         
            Defining_byte = 1'b1;  // regular 
        else if ( i_regf_CMD_ATTR[0] && ( i_regf_DTT == 3'd5 ||  i_regf_DTT == 3'd6 || i_regf_DTT == 3'd7))  
            Defining_byte = 1'b1 ; // immediate      
        else                                                                                                
            Defining_byte = 1'b0 ;
    end 


////////////////////////////////////////// state memory /////////////////////////////////////////////////
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
                regular_counter   = 'd4 ;    // data starts from fifth location
                immediate_counter = 'd2 ;    // data starts from third location
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

                    o_tx_mode = seven_e ;

                    if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin 
                        next_state = PARITY_CMD ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end
                    
                     // erorr state condition is remaining 
                end 
                else begin 
                    o_tx_mode       = serializing_address ;
                    o_txrx_addr_ccc = target_addres ;

                    if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin 
                        next_state = PARITY_CMD ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end
                    
                     // erorr state condition is remaining
                end 
            end

            PARITY_CMD : begin 
                o_tx_en   = 1'b1 ; 
                o_tx_mode = parity_calc ;

                if (i_bitcnt_number == 5'd0 && i_tx_mode_done) begin 
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
                    o_sdahand_pp_od = 1'b0 ;             // open drain 
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
                o_txrx_addr_ccc = i_regf_CMD ;

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
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location + 2 ;                 // third location

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = DEFINING_BYTE ;
                end

                // erorr state condition is remaining   
            end

            ZEROS : begin                               // eight zeros fixed at regfile (e.g location 999)
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location - 1  ;

                if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;

                end
                else begin 
                    next_state = ZEROS ;
                end

                // erorr state condition is remaining   
            end


            PARITY_DATA : begin // parity state any Data word

                if  (i_bitcnt_number == 5'd0 && i_tx_mode_done) begin // if broadcast

                    if (i_frmcnt_last_frame || (Direct_Broadcast_n & first_time)) begin  // crc state only in case of Direct or in case of last data 
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
                
                if (i_bitcnt_number == 5'd1 && i_tx_mode_done) begin 
                    o_tx_en   = 1'b0 ;
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = second_preamble_rx ;
                    o_sdahand_pp_od = 1'b0 ;             // open drain 
                end 
                else begin 
                    o_tx_en   = 1'b1 ; 
                    o_tx_mode = one ;
                end 


                // enable rx and check the target's response
                if (i_bitcnt_number == 5'd2 && i_rx_mode_done && i_rx_second_pre) begin 
                    next_state = FIRST_DATA_BYTE ;
                    //o_tx_en    = 1'b1 ;   
                    //o_rx_en    = 1'b0 ;
                end
                else if (i_bitcnt_number == 5'd2 && i_rx_mode_done && !i_rx_second_pre) begin 
                    next_state = ERROR ;
                end
                else begin
                    next_state = PRE_DATA ;
                end
                
            end


            FIRST_DATA_BYTE : begin    // contains first repeated data byte
                o_tx_en      = 1'b1 ;
                o_regf_rd_en = 1'b1 ;
                if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                    o_tx_mode    = serializing_byte ;
                    o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 4 to point to the fifth location .. reset in CRC or restart
                end 
                else begin // if immediate
                    if (Defining_byte) begin 
                        o_regf_addr = first_location + immediate_counter ; // still takes the third location 
                        o_tx_mode   = serializing_sec_byte_only ;          // as first byte in the third location will contain the Defining Byte
                    end 
                    else begin 
                        o_regf_addr = first_location + immediate_counter ; // 
                        o_tx_mode   = serializing_byte ; 
                    end 
                end 

                if (i_bitcnt_number == 5'd10 && i_tx_mode_done && i_frmcnt_last_frame) begin  // to handle odd number of bytes in both regular and immediate
                    next_state   = ZEROS ; 
                    o_engine_odd = 1'b1 ;       
                end
                else if (i_bitcnt_number == 5'd10 && i_tx_mode_done && !i_frmcnt_last_frame) begin  
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
                    regular_counter = regular_counter + 1 ;
                    if (i_regf_DTT == 3'd3 || i_regf_DTT == 3'd4 || i_regf_DTT == 3'd7) begin  
                        immediate_counter <= immediate_counter + 1 ;                             // intended latch 
                    end 

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
                o_tx_en   = 1'b1 ;
                o_tx_mode = special_preamble ;

                if (i_bitcnt_number == 5'd2 && i_tx_mode_done) begin 
                    o_tx_mode = c_token_CRC ;  
                end
                else if (i_bitcnt_number == 5'd6 && i_tx_mode_done) begin 
                    // tx mode on 5-bits CRC checksum
                    o_tx_mode = value_CRC ;  
                end 
                else if (i_bitcnt_number == 5'd11 && i_tx_mode_done) begin 
                    // tx mode is stalled at 1 (preparing for restart or exit pattern)
                    o_tx_mode = one ; 
                end 
                else if (i_bitcnt_number == 5'd12 && i_tx_mode_done) begin 
                    // finish a command discriptor
                    o_tx_mode = one ;
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
                o_tx_en         = 1'b1 ;
                o_tx_mode       = restart_pattern ;
                o_sclstall_en   = 1'b1 ;
                o_sclstall_code = restart_pattern_stall ;

                if (i_sclstall_stall_done && i_tx_mode_done) begin 
                    next_state = IDLE ;
                end  
                else begin 
                    next_state = RESTART_PATTERN ;
                end
            end 




            EXIT_PATTERN : begin 
                // access timer and staller and tx to perform exit pattern 
                o_tx_en         = 1'b1 ;
                o_tx_mode       = exit_pattern ;
                o_sclstall_en   = 1'b1 ;
                o_sclstall_code = exit_pattern_stall ;

                if (i_sclstall_stall_done && i_tx_mode_done) begin 
                    next_state = IDLE ;
                end  
                else begin 
                    next_state = EXIT_PATTERN ;
                end
            end



/*  
            ERROR : begin                   // to be done

            end 
*/




        endcase
    end
endmodule 



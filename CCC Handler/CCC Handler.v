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
input wire [5:0]  i_bitcnt_number ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire        i_rx_pre ,
input wire        i_sclstall_stall_done ,
input wire        i_rx_error ,  
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
//input wire [15:0] i_regf_DATA_LENGTH , // will be removed 



output reg        o_sclstall_en      ,
output reg [3:0]  o_sclstall_code    ,
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
output reg [15:0] o_regf_addr        , // depends on the depth of the regfile
output reg        o_engine_done      ,
output reg [7:0]  o_txrx_addr_ccc    ,         // new 
output reg        o_engine_odd       ,         // new
output reg [3:0]  o_regf_ERR_STATUS            // new
);   



// internal signals 
reg [4:0] current_state , next_state ;
reg       Direct_Broadcast_n ;               // 1 for direct and 0 for broadcast
reg [6:0] target_addres ;
reg       Defining_byte ; 
reg       first_time ;
reg       controller_abort ; // new by badr (needs to be assigned by some logic)
integer   regular_counter ;
integer   immediate_counter ; 



///////////////////////////////// state encoding //////////////////////////////////////////////

// localparam to prevent overriding the states from outside the design
// as states encoding should never be modified from outside (while instatiation)
// after revision i will convert the coding style to grey
localparam [4:0] IDLE               = 5'd0 ; // 0
localparam [4:0] PRE_CMD            = 5'd1 ; // 1
localparam [4:0] RNW                = 5'd2 ; // 2
localparam [4:0] RESERVED           = 5'd3 ; // 3
//localparam [4:0] FIRST_CMD_BYTE   = 5'b00010 ; // 2
localparam [4:0] SECOND_CMD_BYTE    = 5'd4 ; // 4

localparam [4:0] PARITY_CMD         = 5'd5 ; 
localparam [4:0] PRE_FIRST_DATA_ONE = 5'd6 ; 
localparam [4:0] PRE_FIRST_DATA_TWO = 5'd7 ; 
localparam [4:0] CCC_BYTE           = 5'd8 ; 
localparam [4:0] DEFINING_BYTE      = 5'd9 ; 

localparam [4:0] ZEROS              = 5'd10 ;
localparam [4:0] PARITY_DATA        = 5'd11 ; 
localparam [4:0] PRE_DATA           = 5'd12 ; 
localparam [4:0] FIRST_DATA_BYTE    = 5'd13 ; 

localparam [4:0] SECOND_DATA_BYTE   = 5'd14 ;
localparam [4:0] CRC_STATE          = 5'd15 ; 
localparam [4:0] RESTART_PATTERN    = 5'd16 ; 
localparam [4:0] EXIT_PATTERN       = 5'd17 ; 

localparam [4:0] ERROR              = 5'd18 ; 
localparam [4:0] FINISH             = 5'd19 ; 




localparam [6:0] SEVEN_E = 7'h7E;

// tx modes parameters 
localparam [3:0]  
                zero                   = 4'd0  ,  // 0                       approved by abdo
                one                    = 4'd1  ,  // 1                       approved by abdo
                special_preamble       = 4'd2  ,  // 01 of cmd word          approved by abdo
                seven_zeros            = 4'd3  ,  // 7'b 0000_000            approved by abdo
                serializing_address    = 4'd4  ,  // serializing 7 bits      approved by abdo
                serializing_byte_port  = 4'd5  ,  // serializing 8 bits that given from CCC to tx not from regfile to tx 
                serializing_byte_regf  = 4'd6  ,  //                         approved by abdo
                parity_calc            = 4'd7  ,  //                         approved by abdo
                c_token_CRC            = 4'd8  ,  // 4'hC                    approved by abdo
                value_CRC              = 4'd9  ,  // 5 bit value             approved by abdo
                restart_pattern        = 4'd10 ,  //                         approved by abdo
                exit_pattern           = 4'd11 ;  //                         approved by abdo
                

// regfile parameters 
localparam [11:0] first_location = 12'd1000 ;

// rx parameters 
localparam [3:0] 
                 preamble_rx_mode    = 4'd0 , 
                 parity_check        = 4'd2 ,
                 special_preamble_rx = 4'd3 ,
                 deserializing_byte  = 4'd4 ,
                 check_c_token_CRC   = 4'd5 ,
                 check_value_CRC     = 4'd6 ;


// SCL staller parameters 
localparam [3:0] restart_pattern_stall = 4'b1111 ;
localparam [3:0] exit_pattern_stall    = 4'b1110 ;


// Error states parameters 
localparam [3:0] 
                SUCCESS     = 4'h0  ,
                CRC_ERR     = 4'h1  ,
                PARITY_ERR  = 4'h2  ,
                FRAME       = 4'h3  ,
                ADDR_HEADER = 4'h4  ,
                NACK        = 4'h5  ,
                OVL         = 4'h6  ,
                SRE         = 4'h7  ,
                C_ABORTED   = 4'h8  ,
                T_ABORTED   = 4'h9  ;




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
    o_frmcnt_en        = 1'b1 ; 
    o_sdahand_pp_od    = 1'b1 ; // 1 means PP
    o_regf_wr_en       = 1'b0 ;
    o_regf_rd_en       = 1'b0 ;
    o_regf_addr        = 8'b0 ;
    o_engine_done      = 1'b0 ;


        case (current_state)

            IDLE : begin                     // aw arbitration if needed  
                first_time        = 1'b1 ;   // flag to help to differentiate between the direct and broadcast with assistance of Direct_Braodcast_n flag 
                o_bitcnt_en       = 1'b0 ;
                regular_counter   = 'd8  ;   // data starts from ninth location
                immediate_counter = 'd4  ;   // data starts from forth location
                o_engine_odd      = 1'b0 ;
                controller_abort  = 1'b0 ;
                o_tx_en           = 1'b0 ;
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

                if (i_bitcnt_number == 5'd1 &&i_tx_mode_done) begin 
                    next_state = RNW ;
                end 
                else begin 
                    next_state = PRE_CMD ;
                end

                 // erorr state condition is remaining 

            end 

            RNW : begin
                o_tx_en   = 1'b1 ;
                if (i_bitcnt_number == 5'd2 &&first_time) begin 
                    o_tx_mode = zero ;
                end 
                else begin 
                    if (i_regf_RnW) o_tx_mode = one  ; // read 
                    else            o_tx_mode = zero  ; // write 
                end
                // state transition
                if (i_tx_mode_done) begin 
                    next_state = RESERVED ;
                end
                else begin 
                    next_state = RNW ;
                end
            end 


            RESERVED : begin
                o_tx_en   = 1'b1 ;
                o_tx_mode = seven_zeros ;
                
                // state transition
                if (i_bitcnt_number == 5'd9 &&i_tx_mode_done) begin 
                    next_state = SECOND_CMD_BYTE ;
                end
                else begin 
                    next_state = RESERVED ;
                end
            end 

            SECOND_CMD_BYTE : begin  // contains either 7E or any target address 
                o_tx_en   = 1'b1 ; 
                if (Direct_Broadcast_n && first_time) begin 

                    o_tx_mode = serializing_address ;
                    o_txrx_addr_ccc = SEVEN_E ;

                    if (i_bitcnt_number == 5'd17 &&i_tx_mode_done) begin 
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

                    if (i_tx_mode_done) begin 
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

                if (i_bitcnt_number == 5'd19 && i_tx_mode_done) begin 
                    next_state = PRE_FIRST_DATA_ONE ;
                end
                else begin 
                    next_state = PARITY_CMD ;
                end

                // erorr state condition is remaining 

            end


            PRE_FIRST_DATA_ONE : begin 
            
                o_tx_en   = 1'b1 ;
                o_tx_mode = one ;
                o_rx_en   = 1'b0 ;

                if (i_tx_mode_done) begin
                    next_state = PRE_FIRST_DATA_TWO ;
                    //o_rx_en    = 1'b1 ;
                    o_rx_mode  = preamble_rx_mode ;
                end
                else begin 
                    next_state = PRE_FIRST_DATA_ONE ;
                end 
            
            end 

            PRE_FIRST_DATA_TWO : begin 
                o_tx_en   = 1'b0 ;
                o_rx_en   = 1'b1 ;
                o_rx_mode = preamble_rx_mode ;

                if (i_rx_mode_done && !i_rx_pre) begin
                    next_state = CCC_BYTE ;
                end

                else if (i_rx_mode_done && i_rx_pre) begin 
                    next_state        = ERROR ;
                    o_regf_ERR_STATUS = NACK ;
                end 

                else begin 
                    next_state = PRE_FIRST_DATA_TWO ;
                end 

            end 



/*




            PRE_FIRST_DATA : begin  // should be 10 to mean ACK ,    and 11 is NACK
                    if (i_bitcnt_number == 5'd1 && i_tx_mode_done) begin 
                        o_tx_en   = 1'b0 ;
                        o_rx_en   = 1'b1 ;
                        o_rx_mode = preamble_rx_mode ;
                        //o_sdahand_pp_od = 1'b0 ;             // open drain 
                    end 
                    else begin 
                        o_tx_en   = 1'b1 ; 
                    end 
                    // enable rx and check the target's response
                    if (i_bitcnt_number == 5'd1 && i_rx_mode_done && !i_rx_pre) begin 
                        next_state = CCC_BYTE ;
                        o_tx_en    = 1'b1 ;   
                        o_rx_en    = 1'b0 ;
                    end
                    else if (i_bitcnt_number == 5'd1 && i_rx_mode_done && i_rx_pre) begin 
                        next_state        = ERROR ;
                        o_regf_ERR_STATUS = NACK ;
                        o_tx_en    = 1'b1 ;   
                        o_rx_en    = 1'b0 ;
                    end
                    else begin
                        next_state = PRE_FIRST_DATA ;
                    end
            
            end

*/
            CCC_BYTE : begin    // contains CCC value

                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_port ;
                o_txrx_addr_ccc = i_regf_CMD ;

                if (i_bitcnt_number == 5'd9 && i_tx_mode_done && Defining_byte) begin   // if a defining byte exists
                    next_state = DEFINING_BYTE ;
                end
                else if (i_bitcnt_number == 5'd9 && i_tx_mode_done && !Defining_byte) begin   
                    next_state = ZEROS ; 
                end
                else begin 
                    next_state = CCC_BYTE ;
                end

                // erorr state condition is remaining 

                
            end

            DEFINING_BYTE : begin    // contains definaing byte if exist
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_regf ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location + 2 ;                 // third location

                if (i_bitcnt_number == 5'd17 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = DEFINING_BYTE ;
                end

                // erorr state condition is remaining   
            end

            ZEROS : begin                               // eight zeros fixed at regfile (e.g location 999)
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_regf ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location - 1  ;

                if (i_bitcnt_number == 5'd17 && i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;

                end
                else begin 
                    next_state = ZEROS ;
                end

                // erorr state condition is remaining   
            end


            PARITY_DATA : begin // parity state any Data word
                if (!i_regf_RnW) begin // write 
                    o_tx_en   = 1'b1 ;
                    o_tx_mode = parity_calc ;
                    if  (i_bitcnt_number == 5'd19 && i_tx_mode_done) begin // if broadcast

                        if (i_frmcnt_last_frame || (Direct_Broadcast_n & first_time)) begin  // crc state only in case of Direct or in case of last data 
                            next_state = CRC_STATE ;
                        end 
                        else begin 
                            next_state = PRE_DATA ; // not last byte then continue sending/recieving repeated data 
                        end 
                    end

                    else begin 
                        next_state = PARITY_DATA ;
                    end
                end 
                else begin // read 
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = parity_check ;
                    if  (i_bitcnt_number == 5'd19 && i_rx_mode_done && !i_rx_error) begin 

                        if (i_frmcnt_last_frame || (Direct_Broadcast_n & first_time)) begin  // crc state only in case of Direct or in case of last data 
                            next_state = CRC_STATE ;
                        end 
                        else begin 
                            next_state = PRE_DATA ; // not last byte then continue sending/recieving repeated data 
                        end 
                    end

                    else if (i_bitcnt_number == 5'd19 && i_rx_mode_done && i_rx_error) begin 
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = PARITY_ERR ;
                    end 

                    else begin 
                        next_state = PARITY_DATA ;
                    end
                end 
            end


            PRE_DATA : begin        //  11  means ok continue , and 10 to be aborted 
                if(i_regf_RnW) begin                // read operation from target
                    if (i_bitcnt_number == 5'd0 && i_rx_mode_done) begin 
                        if(i_rx_pre) begin // to check that the first preamble is 1 (else is framing error)
                            o_tx_en   = 1'b1 ;
                            o_rx_en   = 1'b1 ;
                            if(controller_abort) begin
                                o_tx_mode  = zero ; // next state is abort state written below 
                            end
                            else begin 
                                o_tx_mode  = one ; // but OPEN DRAIN ------------------------------- important ---------------------------------
                            end 
                        end 
                        else begin
                            o_tx_en    = 1'b0 ;
                            o_rx_en    = 1'b0 ;
                            next_state = ERROR  ;       // framing error 
                            o_regf_ERR_STATUS = FRAME ;
                        end
                        
                    end 
                    //else if (i_bitcnt_number == 5'd2 && i_rx_mode_done && !i_rx_pre) begin // then it's a short read an i have to go to CRC state

                    //end 
                    else begin 
                        o_rx_en   = 1'b1 ; 
                        o_tx_en   = 1'b0 ;
                        o_rx_mode = preamble_rx_mode ;
                    end 
                    // state transition
                    if (i_bitcnt_number == 5'd1 && i_tx_mode_done && i_rx_pre) begin 
                        next_state = FIRST_DATA_BYTE ;
                        //o_tx_en    = 1'b1 ;   
                        //o_rx_en    = 1'b0 ;
                    end
                    else if (i_bitcnt_number == 5'd1 && i_tx_mode_done && controller_abort) begin 
                        next_state = ERROR ; // abort reading state
                        o_regf_ERR_STATUS = C_ABORTED ;
                    end
                    else begin
                        next_state = PRE_DATA ;
                    end
                end 
                else begin                          // write operation to target

                    if (i_bitcnt_number == 5'd0 && i_tx_mode_done) begin 
                        o_tx_en   = 1'b0 ;
                        o_rx_en   = 1'b1 ;
                        o_rx_mode = preamble_rx_mode ;
                        //o_sdahand_pp_od = 1'b0 ;             // open drain 
                    end 
                    else begin 
                        o_tx_en   = 1'b1 ; 
                        o_tx_mode = one ;
                    end 


                    // enable rx and check the target's response
                    if (i_bitcnt_number == 5'd1 && i_rx_mode_done && i_rx_pre) begin 
                        next_state = FIRST_DATA_BYTE ;
                        //o_tx_en    = 1'b1 ;   
                        //o_rx_en    = 1'b0 ;
                    end
                    else if (i_bitcnt_number == 5'd1 && i_rx_mode_done && !i_rx_pre) begin 
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = T_ABORTED ;
                    end
                    else begin
                        next_state = PRE_DATA ;
                    end
                end 
            end


            FIRST_DATA_BYTE : begin    // contains first repeated data byte
                if (!i_regf_RnW) begin  // write operation 
                    o_tx_en      = 1'b1 ;
                    o_regf_rd_en = 1'b1 ;
                    if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                        o_tx_mode    = serializing_byte_regf ;
                        o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 4 to point to the fifth location 
                    end 
                    else begin // if immediate
                        if (Defining_byte) begin 
                            o_regf_addr = first_location + immediate_counter + 1'b1 ; // for 8 bit width Regfile .. point to fifth location
    
                            o_tx_mode   = serializing_byte_regf ;          // as first byte in the third location will contain the Defining Byte
                        end 
                        else begin 
                            o_regf_addr = first_location + immediate_counter ;        // for 8 bit width Regfile .. point to fourth location
                            o_tx_mode   = serializing_byte_regf ; 
                        end 
                    end 
                end 

                // read operation 
                else begin  
                o_rx_en      = 1'b1 ;
                o_regf_wr_en = 1'b1 ;
                    if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                        o_rx_mode    = deserializing_byte ;
                        o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 4 to point to the fifth location 
                    end 
                    else begin  // there is no immediate case in the read operation 
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = FRAME ;
                    end 
                end

                // for both read and write 
                if (i_bitcnt_number == 5'd10 && (i_rx_mode_done | i_tx_mode_done) && i_frmcnt_last_frame) begin  // to handle odd number of bytes in both regular and immediate
                    next_state   = SECOND_DATA_BYTE ; 
                    o_engine_odd = 1'b1 ;            // to be put in the response discreptor      
                end
                else if (i_bitcnt_number == 5'd10 && (i_rx_mode_done | i_tx_mode_done) && !i_frmcnt_last_frame) begin  
                    next_state = SECOND_DATA_BYTE ; 
                    //immediate_counter = immediate_counter + 1 ;
                    regular_counter   = regular_counter   + 1 ;
                end
                else begin 
                    next_state = FIRST_DATA_BYTE ;
                end

            end


            SECOND_DATA_BYTE : begin   // contains second repeated data byte
                if (!i_regf_RnW) begin // write operation 
                    o_tx_en      = 1'b1 ;
                    o_regf_rd_en = 1'b1 ;
                    o_tx_mode    = serializing_byte_regf ;
                    if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                        o_regf_addr  = first_location + regular_counter ; 
                    end
                    else begin 
                        o_regf_addr  = first_location + immediate_counter ; 
                    end 
                    if (i_bitcnt_number == 5'd18 && i_tx_mode_done) begin   
                        next_state = PARITY_DATA ;
                        // no need to put conditions , immediated and regular can't happen together
                        immediate_counter = immediate_counter + 1 ;
                        regular_counter   = regular_counter   + 1 ;
                    end
                    else begin 
                        next_state = SECOND_DATA_BYTE ;
                    end 
                end 
                else begin  // read operation 
                    o_rx_en      = 1'b1 ;
                    o_regf_wr_en = 1'b1 ;
                    o_rx_mode    = deserializing_byte ;
                    if (!i_regf_CMD_ATTR[0]) begin                          // if regular command discriptor  
                        o_regf_addr  = first_location + regular_counter ; 
                    end
                    else begin  // there is no immediate case in the read operation 
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = FRAME ;
                    end 
                    if (i_bitcnt_number == 5'd18 && i_rx_mode_done ) begin   
                        next_state = PARITY_DATA ;
                        // no need to put conditions , immediated and regular can't happen together
                        //immediate_counter = immediate_counter + 1 ;
                        regular_counter   = regular_counter   + 1 ;
                    end 
                    else begin 
                        next_state = SECOND_DATA_BYTE ;
                    end
                end     
            end
        

            CRC_STATE : begin                  // this state can handle the rest of the CRC word (2 + 4 + 5 + 1)
                if (!i_regf_RnW) begin  // write 
                    o_tx_en   = 1'b1 ;
                    if (i_bitcnt_number < 5'd2) begin 
                        // tx mode on preamble 01  
                        o_tx_mode = special_preamble ;
                    end 
                    else if ((i_bitcnt_number >= 5'd2 && i_bitcnt_number < 5'd6) && i_tx_mode_done) begin 
                        o_tx_mode = c_token_CRC ;  
                    end
                    else if ((i_bitcnt_number >= 5'd6 && i_bitcnt_number < 5'd11) && i_tx_mode_done) begin 
                        // tx mode on 5-bits CRC checksum
                        o_tx_mode = value_CRC ;  
                    end 

               
                    else if (i_bitcnt_number == 5'd11 && i_tx_mode_done) begin 
                        // finish a command discriptor
                        o_tx_mode = one ;
                 
                        if (Direct_Broadcast_n && first_time) begin 
                            next_state    = RESTART_PATTERN ;
                            o_engine_done = 1'b0 ;
                            first_time    = 1'b0 ;
                        end 
                        else begin 
                            if (!i_regf_TOC) begin 
                                next_state = RESTART_PATTERN ;
                                //o_engine_done = 1'b1 ;
                            end 
                    
                            else begin 
                                next_state = EXIT_PATTERN ;
                                //o_engine_done = 1'b1 ;
                            end 
                        end 
                    end

                    else begin 
                        next_state = CRC_STATE ;
                    end
                end  
                    //////////////////////////////////////////// READ //////////////////////////////////////////////
                else begin  // read  
                    o_rx_en   = 1'b1 ;
                    if (i_bitcnt_number < 5'd2) begin 
                        // rx mode on preamble 01  
                        o_rx_mode = special_preamble_rx ;
                    end 
                    else if ((i_bitcnt_number >= 5'd2 && i_bitcnt_number < 5'd6) && i_rx_mode_done) begin 
                        o_rx_mode = check_c_token_CRC ;  
                    end
                    else if ((i_bitcnt_number >= 5'd6 && i_bitcnt_number < 5'd11) && i_rx_mode_done) begin 
                        // rx mode on 5-bits CRC checksum
                        o_rx_mode = check_value_CRC ;  
                    end 

               
                    else if (i_bitcnt_number == 5'd11 && i_rx_mode_done) begin 
                        // check CRC error 
                        if (i_rx_error) begin 
                            next_state        = ERROR ;
                            o_regf_ERR_STATUS = CRC_ERR ;
                        end 
                        
                        else if (Direct_Broadcast_n && first_time) begin 
                            next_state    = RESTART_PATTERN ;
                            o_engine_done = 1'b0 ;
                            first_time    = 1'b0 ;
                        end 
                        else begin 
                            if (!i_regf_TOC) begin 
                                next_state = RESTART_PATTERN ;
                                //o_engine_done = 1'b1 ;
                            end 
                    
                            else begin 
                                next_state = EXIT_PATTERN ;
                                //o_engine_done = 1'b1 ;
                            end 
                        end 
                    end

                    else begin 
                        next_state = CRC_STATE ;
                    end
                end     
            end

            RESTART_PATTERN : begin 
                // access timer and staller and tx to perform restart pattern 
                o_tx_en         = 1'b1 ;
                o_tx_mode       = restart_pattern ;
                o_sclstall_en   = 1'b1 ;
                o_sclstall_code = restart_pattern_stall ;

                if (i_sclstall_stall_done && i_tx_mode_done && i_frmcnt_last_frame) begin 
                    next_state = FINISH ;
                end 
                else if (i_sclstall_stall_done && i_tx_mode_done && !i_frmcnt_last_frame) begin 
                    next_state = PRE_CMD ;
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
                o_bitcnt_err_rst = 1'b0 ;
                if (i_sclstall_stall_done && i_tx_mode_done) begin 
                    next_state = FINISH ;
                end  
                else begin 
                    next_state = EXIT_PATTERN ;
                end
            end



 
            ERROR : begin      // controller error state 
                o_bitcnt_err_rst = 1'b1 ; // active hight rst to count specially for error state

                o_tx_en   = 1'b1 ;
                o_tx_mode = one ;
                if(i_bitcnt_number == 37) begin 
                    next_state = EXIT_PATTERN ; // may issue exit or restart pattern .. but conditions ?
                end 
                else begin 
                    next_state = ERROR ;
                end 

            end 

            

            FINISH : begin 
                first_time        = 1'b1 ;   // flag to help to differentiate between the direct and broadcast with assistance of Direct_Braodcast_n flag 
                o_bitcnt_en       = 1'b0 ;
                regular_counter   = 'd4  ;   // data starts from fifth location
                immediate_counter = 'd2  ;   // data starts from third location
                o_engine_odd      = 1'b0 ;
                controller_abort  = 1'b0 ;
                o_engine_done     = 1'b1 ;
                
                o_regf_ERR_STATUS = SUCCESS ;
                next_state = IDLE ;


            end 


        endcase
    end
endmodule 



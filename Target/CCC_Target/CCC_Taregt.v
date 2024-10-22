
/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Fatma Saad
 
 Revision:   

 Version : 1.0

 Create Date: 16/4/2024
 Design Name: Common Command Code of Target
 Module Name: CCC_Target

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
module CCC_Target(

input wire        i_sys_clk ,
input wire        i_sys_rst ,
input wire        i_engine_en ,
input wire        i_tx_mode_done ,
input wire        i_rx_mode_done ,
input wire        i_exit_done ,
input wire        i_restart_done ,
input wire        i_RnW ,
input wire [15:0] i_regf_MWL ,
input wire [15:0] i_regf_MRL ,
input wire [7:0]  i_CCC_value ,
input wire [7:0]  i_Def_byte ,
input wire        i_rx_error , //error in special preamble after restart CMND word or parity or crc value or token crc or my addrest_or_not

input wire        premable,

output reg        o_tx_en ,
output reg [2:0]  o_tx_mode ,
output reg        o_rx_en ,
output reg [3:0]  o_rx_mode ,
output reg        o_detector_en ,
output reg        o_engine_done ,
output reg [7:0]  o_regf_addr ,
output reg        o_regf_wr_en ,
output reg        o_regf_rd_en 


);


// internal signals 
reg [3:0] current_state , next_state ;
reg case_ccc, direc_ccc ;
reg [2:0] byte_no ;


// Local Parameters of States
localparam [3:0] IDLE = 5'd0 ; 
localparam [3:0] PRE_CMD = 5'd1 ;
localparam [3:0] CHECK_CCC = 5'd2 ;
localparam [3:0] DEF_DATA = 5'd3 ;
localparam [3:0] CHECK_PARITY = 5'd4 ;
localparam [3:0] DATA= 5'd5 ;
localparam [3:0] SPECIAL_PREAMBLE = 5'd6 ;
localparam [3:0] DESER_ZEROS = 5'd7 ;
localparam [3:0] ACK = 5'd8 ;
localparam [3:0] TOKEN_CRC = 5'd9 ;
localparam [3:0] CRC_VALUE = 5'd10 ;
localparam [3:0] RESTART_EXIT = 5'd11 ;
localparam [3:0] DESER_ADDR = 5'd12 ;

//Local Parameters of TX modes
localparam [2:0] one_preamble = 3'b000 ; //confirmed with TX
localparam [2:0] zero_preamble = 3'b001 ; //confirmed with TX




//Local Parameters of RX modes
localparam [3:0] preamble = 4'b0001 ; //confirmed with RX
localparam [3:0] ccc_value = 4'b0110 ; //confirmed with RX
localparam [3:0] deser_def = 4'b0010 ; //confirmed with RX to send data and def byte(useless addr) on same state
localparam [3:0] check_parity = 4'b0100 ; //confirmed with RX
localparam [3:0] special_preamble = 4'b1001; //confirmed with RX
localparam [3:0] deser_zeros = 4'b1000 ; //confirmed with RX
localparam [3:0] deser_addr = 4'b0111 ; //confirmed with RX
localparam [3:0] token_crc = 4'b0101 ; //confirmed with R
localparam [3:0] crc_value = 4'b0110; //confirmed with RX



/////////////////////////////////////////parameters of regf
localparam [7:0] useless_addr_def_byte = 8'b1111_1111;
localparam [7:0] first_byte_MWL = 8'd0;
localparam [7:0] second_byte_MWL = 8'd1;
localparam [7:0] first_byte_MRL = 8'd2;
localparam [7:0] second_byte_MRL = 8'd3;




/////////////////////////// state transition ///////////////////////
    always @(posedge i_sys_clk or negedge i_sys_rst) begin
        if (!i_sys_rst) begin
            current_state <= IDLE ;
        end
        else  begin
            current_state <= next_state ;
        end
    end
//////////////////////////////////next state logic and output logic ///////////////////////
always@(*)begin

    // initial values of outputs 
    o_tx_en            = 1'b0 ; 
    o_tx_mode          = 3'b0 ; 
    o_rx_en            = 1'b0 ; 
    o_rx_mode          = 4'b0 ; 
    o_regf_wr_en       = 1'b0 ;
    o_regf_rd_en       = 1'b0 ;
    o_regf_addr        = 8'b0 ;
    o_engine_done      = 1'b0 ;
    byte_no            = 3'd0 ;
    case_ccc           = 1'b0 ;
    direc_ccc          = 1'b0 ;
    o_detector_en      = 1'b0 ;

        case (current_state)

            IDLE : begin

                if (i_engine_en) begin 
                    
                    o_rx_en    = 1'b1 ; 
                    o_rx_mode  = preamble ; 
                    next_state = PRE_CMD ;

                end
                else begin 
                    next_state = IDLE ;
                end 

            end 

            PRE_CMD : begin
                if (i_engine_en) begin 
                    if (i_rx_mode_done && !preamble && i_restart_done) begin ///w/r bit 
                        o_rx_en = 1'b1 ;
                        o_rx_mode = deser_zeros ;
                        next_state = DESER_ZEROS ;
                    end
                    else if (i_rx_mode_done && premable) begin 
                        o_rx_en = 1'b0 ;
                        o_tx_en = 1'b1 ;
                        o_tx_mode = zero_preamble ;  //accept send 0 or reject send 1 with Ma8raby
                        next_state = ACK ;
                    end
                    else if (i_rx_mode_done && !preamble) begin
                        o_rx_en = 1'b0 ;
                        o_engine_done      = 1'b1 ;
                        next_state = IDLE ;
                    end
                    else
                        next_state = PRE_CMD ;
                end
                else
                    next_state = IDLE ;
            end 
            ACK : begin
                if (i_tx_mode_done /*accepts*/) begin
                    o_tx_en = 1'b0 ;
                    o_rx_en = 1'b1 ;

                    if (case_ccc) begin
                        o_rx_mode = deser_def ; //used to deser data of DATA WRD
                        o_regf_wr_en = 1'b1 ;

                        if (i_CCC_value == 8'h09)
                            o_regf_addr = first_byte_MWL ; //address of MWL 
                        else if (i_CCC_value ==8'h0A) 
                            o_regf_addr = first_byte_MRL ; //address of MRL 
                        //else if (i_CCC_value == )
                        next_state = DATA ;
                    end
                    else begin
                        o_rx_mode = ccc_value ;
                        next_state = CHECK_CCC ;
                    end
                end 
                else if (i_tx_mode_done /*rejects*/) begin
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end
                else
                    next_state = ACK ;

            end
            CHECK_CCC : begin
            if (i_rx_mode_done) begin
                if (i_CCC_value== 8'h00 || i_CCC_value== 8'h01 || i_CCC_value== 8'h80 || i_CCC_value== 8'h81 || 
                i_CCC_value== 8'h09 || i_CCC_value== 8'h0A || i_CCC_value== 8'h89 || i_CCC_value== 8'h8B ||
                i_CCC_value== 8'h8A || i_CCC_value== 8'h8C || i_CCC_value== 8'h90 || i_CCC_value== 8'h2A ||
                i_CCC_value== 8'h9A || i_CCC_value== 8'h8D || i_CCC_value== 8'h8E || i_CCC_value== 8'h8F ) begin //8'h00 ENEC_BC
                    //in case of direct flag direct_ccc= 1
                    o_rx_en = 1'b1 ; //we need to set direct_ccc flag =1 here******************************
                    o_regf_addr = useless_addr_def_byte;  //address to save def in useless address
                    o_regf_wr_en = 1'b1 ;
                    o_rx_mode = deser_def ; //DEFbyte deserializing
                    next_state = DEF_DATA ;
                end
                /*else if (i_CCC_value== 0x01) begin //DISEC_BC
                    /* code 
                end
                else if (i_CCC_value== 0x80) begin //ENEC_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x81) begin //DISEC_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x80) begin //ENEC_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x09) begin //SETMWL_BC
                    /* code 
                end
                else if (i_CCC_value== 0x0A) begin //SETMRL_BC
                    /* code 
                end
                else if (i_CCC_value== 0x89) begin //SETMWL_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8B) begin //GETMWL_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8A) begin //SETMRL_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8C) begin //GETMRL_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x90) begin //GETSTATUS_Dir format 1
                    /* code 
                end
                else if (i_CCC_value== 0x2A) begin //RSTACT_BC
                    /* code 
                end
                else if (i_CCC_value== 0x9A) begin //RSTACT_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8D) begin //GETPID_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8E) begin //GETBCR_Dir
                    /* code 
                end
                else if (i_CCC_value== 0x8F) begin //GETDCR_Dir
                    /* code 
                end*/
                else
                begin 
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end

            end 
            else
                next_state = CHECK_CCC ;
            end
            DEF_DATA : begin
                o_regf_wr_en = 1'b0;
                if (i_rx_mode_done) begin
                    
                        o_rx_en = 1'b1 ;
                        o_rx_mode = check_parity ;
                        next_state = CHECK_PARITY ;
                end 
                else
                    next_state = DEF_DATA ;

            end

            CHECK_PARITY : begin
                if (i_rx_mode_done && !i_rx_error) begin
                    o_rx_en = 1'b1 ;
                    //if (/*i_CCC_value == 8'h00 || i_CCC_value== 8'h01 || i_CCC_value== 8'h09 || i_CCC_value== 8'h0A || i_CCC_value== 8'h2A====BC*/ ) begin /////BCCCCC
                        if (case_ccc || direc_ccc) begin 
                            o_rx_mode = special_preamble ;
                            next_state = SPECIAL_PREAMBLE ;
                        end

                        else begin
                            o_rx_mode = preamble ;
                            next_state = PRE_CMD ;
                            case_ccc = 1'b1; //first timee to set this flag=1
                        end 
                    //end
                    
                end 
                else if (i_rx_mode_done && i_rx_error) begin
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end 
                else 
                    next_state = CHECK_PARITY ;
            end 
            DATA : begin
                if (i_rx_mode_done) begin
                    if (i_CCC_value == 8'h09 && (byte_no==3'd2) ) begin 
                        byte_no = 3'd0 ;  
                        o_rx_en = 1'b1 ;
                        o_rx_mode = check_parity ;
                        next_state = CHECK_PARITY ;
                        
                    end
                    else if (i_CCC_value== 8'h09 ) begin
                        o_rx_en = 1'b1 ;
                        o_regf_wr_en = 1'b1;
                        o_regf_addr = second_byte_MWL ; //second 8 after 
                        byte_no = 3'd2 ;
                        next_state = DATA ;
                    end 
                    /*else if (i_CCC_value == 8'h00 & (byte_no==3'd2) ) begin
                        o_rx_en = 1'b1 ;
                        o_rx_mode = check_parity ;
                        next_state = CHECK_PARITY ;
                        byte_no = 3'd0 ;
                    end
                    /*else if (i_CCC_value== 8'h00 ) begin
                        o_rx_en = 1'b1 ;
                        o_regf_wr_en = 1'b1;
                        o_regf_addr = second_byte_MRL ;
                        byte_no = 3'd2 ;
                        next_state = DATA ;
                    end*/
                    else if (i_CCC_value == 8'h0A && (byte_no==3'd2) ) begin
                        o_rx_en = 1'b1 ;
                        o_rx_mode = check_parity ;
                        next_state = CHECK_PARITY ;
                        byte_no = 3'd0 ;
                    end
                    else if (i_CCC_value== 8'h0A ) begin
                        o_rx_en = 1'b1 ;
                        o_regf_wr_en = 1'b1;
                        o_regf_addr = second_byte_MRL ;
                        byte_no = 3'd2 ;
                        next_state = DATA ;
                    end
                    else begin
                        o_engine_done = 1'b1 ;
                        next_state = IDLE ;
                    end
                end
                else
                    next_state = DATA ;

            end 
            SPECIAL_PREAMBLE : begin 
                if (i_rx_mode_done) begin
                   o_rx_en = 1'b1 ;
                   o_rx_mode = token_crc ;
                   next_state = TOKEN_CRC ;
                end 
                else
                    next_state = SPECIAL_PREAMBLE ;

            end 

            TOKEN_CRC : begin
                if (i_rx_mode_done && !i_rx_error) begin
                   o_rx_en = 1'b1 ;
                   o_rx_mode = crc_value ;
                   next_state = CRC_VALUE ;
                end
                else if (i_rx_mode_done && i_rx_error) begin
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end
                else
                    next_state = TOKEN_CRC ;
            end
            CRC_VALUE : begin ///eh fr2 7asl error wla l2 f case crc_value??????************
                if (i_rx_mode_done && !i_rx_error) begin
                    case_ccc = 1'b0 ;
                   o_rx_en = 1'b0 ;
                   next_state = RESTART_EXIT ; //must n't go to idle it must support end procedure************
                end
                else if (i_rx_mode_done && i_rx_error) begin
                    case_ccc = 1'b0 ;
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end
                else if (i_rx_mode_done && !i_rx_error && direc_ccc ) begin
                    o_rx_en = 1'b0 ;
                    o_detector_en = 1'b1 ;
                    next_state = RESTART_EXIT ;
                end
                else
                    next_state = CRC_VALUE ;
            end 

            RESTART_EXIT : begin
                if (i_restart_done) begin
                        o_rx_en = 1'b1 ;
                        o_rx_mode = preamble ;
                        next_state = PRE_CMD ;
                end
                //else if (i_exit_done)
            end
            DESER_ZEROS : begin
                if (i_rx_mode_done) begin
                    o_rx_en = 1'b1 ;
                    o_rx_mode = deser_addr ;
                    next_state = DESER_ADDR ;
                end

                else
                    next_state = DESER_ZEROS ;


            end
            DESER_ADDR : begin
                if (i_rx_mode_done && !i_rx_error) begin //error is sent when rx know it is my address or not
                    o_rx_en = 1'b1 ;
                    o_rx_mode = check_parity ;
                    next_state = CHECK_PARITY ; //////***********************////////////
                end
                else begin
                    o_rx_en = 1'b0 ;
                    o_engine_done = 1'b1 ;
                    next_state = IDLE ;
                end


            end  
        endcase 
    end 
        endmodule 
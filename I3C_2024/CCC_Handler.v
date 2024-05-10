/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Omar Mohammed Badr
 
 Revision:   

 Version : 1.0

 Create Date: 12/2/2024
 Design Name: Common Command Code Handler
 Module Name: CCC_Handler

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
input wire        i_i_regf_RnW       ,          
input wire [2:0]  i_i_regf_CMD_ATTR  ,
input wire [7:0]  i_i_regf_CMD       ,          // CCC value 
input wire [4:0]  i_i_regf_DEV_INDEX ,
input wire        i_i_regf_TOC       , 
input wire        i_i_regf_WROC      , 

// in case of immidiate command descriptor 
input wire [2:0]  i_i_regf_DTT       , 

// in case of regular command descriptor 
input wire        i_i_regf_DBP       , 
input wire        i_i_regf_SRE       , 
//input wire [15:0] i_regf_DATA_LENGTH , // will be removed 

// new for CCC Table 
//input wire [4:0] i_no_of_targets ,

output reg        o_frmcnt_Direct_Broadcast_n ,
output reg        o_sclstall_en      ,
output reg [4:0]  o_sclstall_code    ,
output reg        o_tx_en            ,
output reg [3:0]  o_tx_mode          ,
output reg        o_rx_en    ,
output reg [3:0]  o_rx_mode  ,

//output reg        o_rx_en_negedge    ,
//output reg [3:0]  o_rx_mode_negedge  ,


output reg        o_bitcnt_en        ,
output reg        o_bitcnt_err_rst   , 
output reg        o_frmcnt_en        ,
output reg        o_sdahand_pp_od    ,
output reg        o_regf_wr_en       ,
output reg        o_regf_rd_en       ,
output reg [11:0] o_regf_addr        , // depends on the depth of the regfile
output reg        o_engine_done      ,
output reg [7:0]  o_txrx_addr_ccc    ,         
output reg        o_engine_odd       ,         
output reg [3:0]  o_regf_ERR_STATUS            
);   



// internal signals 
reg [4:0] current_state , next_state ;
reg       Direct_Broadcast_n     = 1'b0 ;                      // 1 for direct and 0 for broadcast
reg       Direct_Broadcast_n_del = 1'b0 ;           // delayed version of the above signal
wire [6:0] target_addres ;
reg       Defining_byte ; 
reg       first_time ;
reg       controller_abort ; // new by badr (needs to be assigned by some logic)
integer   regular_counter ;
integer   immediate_counter ; 
reg [9:0] tmp_shift ;
//reg [3:0] o_rx_mode ;
//reg       o_rx_en ;


// configuration 
reg        i_regf_RnW       ;  
reg [2:0]  i_regf_CMD_ATTR  ;
reg [7:0]  i_regf_CMD       ;
reg [4:0]  i_regf_DEV_INDEX ;
reg        i_regf_TOC       ;
reg        i_regf_WROC      ;
reg [2:0]  i_regf_DTT       ;
reg        i_regf_DBP       ;
reg        i_regf_SRE       ;














///////////////////////////////// state encoding //////////////////////////////////////////////

// localparam to prevent overriding the states from outside the design
// as states encoding should never be modified from outside (while instatiation)
// after revision i will convert the coding style to grey
localparam  [4:0]  IDLE               = 5'd0  , // 0
                   PRE_CMD            = 5'd1  , // 1
                   RNW                = 5'd2  , // 2
                   RESERVED           = 5'd3  , // 3
                   SECOND_CMD_BYTE    = 5'd4  , // 4
                   PARITY_CMD         = 5'd5  , 
                   PRE_FIRST_DATA_ONE = 5'd6  , 
                   PRE_FIRST_DATA_TWO = 5'd7  , 
                   CCC_BYTE           = 5'd8  , 
                   DEFINING_BYTE      = 5'd9  , 
                   ZEROS              = 5'd10 ,
                   PARITY_DATA        = 5'd11 ,
                   PRE_DATA_ONE       = 5'd12 ,
                   PRE_DATA_TWO       = 5'd13 , 
                   FIRST_DATA_BYTE    = 5'd14 , 
                   SECOND_DATA_BYTE   = 5'd15 ,
                   C_TOKEN_STATE      = 5'd16 , 
                   CRC_CHECKSUM_STATE = 5'd17 , 
                   RESTART_PATTERN    = 5'd18 , 
                   EXIT_PATTERN       = 5'd19 , 
                   ERROR              = 5'd20 , 
                   FINISH             = 5'd21 , 
                   PRE_CRC_TARGET     = 5'd22 ,
                   RESTART_PATTERN_SPECIAL = 5'd23 ;

parameter [6:0] SEVEN_E = 7'h7E ;

// tx modes parameters 
parameter [3:0]  
                zero                   = 4'd6  ,  //                        
                one                    = 4'd2  ,  //                        
                special_preamble       = 4'd0  ,  // 01 of cmd word          
                seven_zeros            = 4'd3  ,  // 7'b 0000_000            
                serializing_address    = 4'd1  ,  // serializing 7 bits + 1 bit ParAdj      
                serializing_byte_port  = 4'd5  ,  // serializing 8 bits that given from CCC to tx not from regfile to tx 
                serializing_byte_regf  = 4'd7  ,  //                         
                parity_calc            = 4'd4  ,  //                        
                c_token_CRC            = 4'd12 ,  // 4'hC                    
                value_CRC              = 4'd13 ,  // 5 bit value             
                restart_pattern        = 4'd15 ,  //                         
                exit_pattern           = 4'd14 ;  //                         
                

// regfile parameters 
parameter [11:0] first_location = 12'd1000 ;

// rx parameters 
parameter [3:0] 
                 preamble_rx_mode    = 4'd0 , 
                 CRC_PREAMBLE        = 4'd1 ,
                 parity_check        = 4'd6 ,
                 deserializing_byte  = 4'd3 ,
                 check_c_token_CRC   = 4'd5 ,
                 check_value_CRC     = 4'd7 ;


// SCL staller parameters 
parameter [4:0] restart_pattern_stall = 5'd12  , // according to restart pattern specs 
                restart_pattern_stall_special = 5'd11  , // according to restart pattern specs
                exit_pattern_stall    = 5'd17 ; // according to exit pattern specs 


// Error states parameters 
parameter [3:0] 
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
// CCC values 
parameter [7:0] 
                ENEC_D      = 8'h80 ,   
                DISEC_D     = 8'h81 , 
                SETMWL_D    = 8'h89 ,
                SETMRL_D    = 8'h8A ,
                GETMWL_D    = 8'h8B ,
                GETMRL_D    = 8'h8C ,
                GETSTATUS_D = 8'h90 ,
                GETPID_D    = 8'h8D ,
                GETBCR_D    = 8'h8E ,
                GETDCR_D    = 8'h8F ,
                ENEC_B      = 8'h00 ,
                DISEC_B     = 8'h01 ,
                SETMWL_B    = 8'h09 ,
                SETMRL_B    = 8'h0A ,
                Dummy_B     = 8'h1F ;


always @(*) begin 
    o_frmcnt_Direct_Broadcast_n = Direct_Broadcast_n ;
end 

/////////////////////////// decoding the device address  ///////////////////////////////////////

assign target_addres = i_regf_DEV_INDEX + 'd8 ;
/*
localparam [3:0] no_of_unq_ccc_sup = 4'd9 ;

localparam [5:0] CCC_value_hi      = 7'd63 ,
                 CCC_value_lo      = 7'd56 ,
                 Def_byte_hi       = 7'd55 ,
                 Def_byte_lo       = 7'd48 ,
                 Data_one_hi       = 7'd47 ,
                 Data_one_lo       = 7'd40 ,
                 Data_two_hi       = 7'd39 ,
                 Data_two_lo       = 7'd32 ,
                 Data_three_hi     = 7'd31 ,
                 Data_three_lo     = 7'd24 ,
                 Data_four_hi      = 7'd23 ,
                 Data_four_lo      = 7'd16 ,
                 Data_five_hi      = 7'd15 ,
                 Data_five_lo      = 7'd8  ,
                 Data_six_hi       = 7'd7  ,
                 Data_six_lo       = 7'd0  ;

    generate 
        genvar i ;
        for (i = 0 ; i < i_no_of_targets ; i = i + 1) begin
            reg [63:0] CCC_Table [no_of_unq_ccc_sup:0][i] ;
        end 
    endgenerate

*/


//////////////////////////////////////// Direct or Broadcat detection  ///////////////////////////////////////////////

// we have 16 required CCC to support at ground level 

// to determine whether it's a Direct or Broadcast 
    always @(*) begin 
        case (i_regf_CMD) 
            8'h80 : Direct_Broadcast_n = 1'b1 ;   // ENEC     
            8'h81 : Direct_Broadcast_n = 1'b1 ;   // DISEC       
            8'h89 : Direct_Broadcast_n = 1'b1 ;   // SETMWL        
            8'h8A : Direct_Broadcast_n = 1'b1 ;   // SETMRL        
            8'h8B : Direct_Broadcast_n = 1'b1 ;   // GETMWL          
            8'h8C : Direct_Broadcast_n = 1'b1 ;   // GETMRL        
            8'h90 : Direct_Broadcast_n = 1'b1 ;   // GETSTATUS  
            8'h8D : Direct_Broadcast_n = 1'b1 ;   // GETPID       
            8'h8E : Direct_Broadcast_n = 1'b1 ;   // GETBCR        
            8'h8F : Direct_Broadcast_n = 1'b1 ;   // GETDCR      

            8'h00 : Direct_Broadcast_n = 1'b0 ;   // ENEC      (broadcast version)
            8'h01 : Direct_Broadcast_n = 1'b0 ;   // DISEC     (broadcast version)
            8'h09 : Direct_Broadcast_n = 1'b0 ;   // SETMWL    (broadcast version)
            8'h0A : Direct_Broadcast_n = 1'b0 ;   // SETMRL    (broadcast version)
           

            8'h1F : Direct_Broadcast_n = 1'b0 ;    // Dummy CCC value for end procedure
            default : Direct_Broadcast_n = 1'b0 ;  // broadcast by default
        endcase
    end

 always @ (posedge i_sys_clk or negedge i_sys_rst) begin 
    if (!i_sys_rst) begin
        tmp_shift <= 10'd0 ;
        Direct_Broadcast_n_del <= 1'b0 ;



    end 
    else begin 
        if (i_engine_en) begin 
            tmp_shift[0] <= Direct_Broadcast_n ;
            tmp_shift[9:1] <= tmp_shift [8:0] ;
            Direct_Broadcast_n_del <= tmp_shift[9] ; // delayed 8 system clk cycles 
        end 
        else begin 
            Direct_Broadcast_n_del <= 1'b0 ;
            tmp_shift <= 10'd0 ;
        end  
    end   
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


////////////////////////////////////////// state memory ////////////////////////////////////////////////

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

    // initial values of outputs INTENTINAL LATCH that can be easily removed if STA analysis is fired 

    o_sclstall_en      = 1'b0 ;  
    o_sclstall_code    = 8'b0 ; 
    o_tx_en            = 1'b0 ; 
    o_tx_mode          = 4'b0 ; 
    o_rx_en            = 1'b0 ; 
    o_rx_mode          = 4'b0 ; 
    o_bitcnt_en        = 1'b1 ; // enabled in all states except for idle state
    o_bitcnt_err_rst   = 1'b0 ; 
    o_sdahand_pp_od    = 1'b1 ; // 1 means PP
    o_regf_wr_en       = 1'b0 ;
    o_regf_rd_en       = 1'b0 ;
    o_engine_done      = 1'b0 ;


        case (current_state)

            IDLE : begin                     // aw arbitration if needed  
                // sampling the configuration once a sequence
                
                i_regf_RnW       = i_i_regf_RnW       ;
                i_regf_CMD_ATTR  = i_i_regf_CMD_ATTR  ;
                i_regf_CMD       = i_i_regf_CMD       ;
                i_regf_DEV_INDEX = i_i_regf_DEV_INDEX ;
                i_regf_TOC       = i_i_regf_TOC       ;
                i_regf_WROC      = i_i_regf_WROC      ;
                i_regf_DTT       = i_i_regf_DTT       ;
                i_regf_DBP       = i_i_regf_DBP       ;
                i_regf_SRE       = i_i_regf_SRE       ;

                first_time        = 1'b1 ;   // flag to help to differentiate between the direct and broadcast with assistance of Direct_Braodcast_n flag 
                o_bitcnt_en       = 1'b0 ;
                regular_counter   = 'd8  ;   // data starts from ninth location
                immediate_counter = 'd4  ;   // data starts from forth location
                o_engine_odd      = 1'b0 ;
                controller_abort  = 1'b0 ;
                o_tx_en           = 1'b0 ;
                o_frmcnt_en       = 1'b0 ;

                if (i_engine_en) begin 
                    next_state = PRE_CMD ;
                    o_tx_en    = 1'b1 ; 
                    o_tx_mode  = special_preamble ; 
                end
                else begin 
                    next_state = IDLE ;
                end 

            end 

            PRE_CMD : begin // i'm driving the 2 bits with 2'b01
                if (i_engine_en) begin 
                    o_tx_en   = 1'b1 ; 
                    o_tx_mode = special_preamble ; 

                    if (i_tx_mode_done && !(i_frmcnt_last_frame || (Direct_Broadcast_n_del && first_time))) begin   
                        next_state = RNW ;
                    end 
                    else if ((i_tx_mode_done || (i_rx_mode_done && !i_rx_error)) && (i_frmcnt_last_frame  || (Direct_Broadcast_n_del && first_time))) begin  // at reading operation with matched data length
                        next_state = C_TOKEN_STATE ;
                    end
                    else if ((i_tx_mode_done || (i_rx_mode_done && i_rx_error)) && (i_frmcnt_last_frame  || (Direct_Broadcast_n_del && first_time))) begin  // at reading operation with matched data length
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = FRAME ;
                    end
                    else begin 
                        next_state = PRE_CMD ;
                    end
                end 
                else begin
                    next_state = IDLE ;
                end
            end 

            PRE_CRC_TARGET : begin // target is driving the 2 bits with 2'b01
                if (i_engine_en) begin
                    o_rx_en   = 1'b1 ; 
                    o_rx_mode = parity_check ;

                    if ((i_rx_mode_done ) && i_frmcnt_last_frame) begin  // HENAAAAAAAAAAAAAA PUT THE CONDITION AFTER VERIFICATIONS (i_rx_mode_done && ! rx_err)
                        next_state = C_TOKEN_STATE ;
                    end
                    else if (i_rx_mode_done ) begin  // at reading operation with matched data length    HENA BARDO PUT THE CONDITION (i_rx_mode_done && rx_err)
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = FRAME ;
                    end
                    else begin 
                        next_state = PRE_CRC_TARGET ;
                    end
                end 
                else begin 
                    next_state = IDLE ;
                end 
            end 

            RNW : begin
                o_tx_en   = 1'b1 ;
                if (first_time) begin 
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
                if (i_tx_mode_done) begin 
                    next_state = SECOND_CMD_BYTE ;
                end
                else begin 
                    next_state = RESERVED ;
                end
            end 

            SECOND_CMD_BYTE : begin  // contains either 7E or any target address 
                o_tx_en   = 1'b1 ; 
                if (first_time) begin 

                    o_tx_mode = serializing_address ;
                    o_txrx_addr_ccc = SEVEN_E ;

                    if (i_tx_mode_done) begin 
                        next_state = PARITY_CMD ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end       
                end 
                else if (Direct_Broadcast_n_del && !first_time) begin 
                    o_frmcnt_en     = 1'b1 ;                    // new 
                    o_tx_mode       = serializing_address ;
                    o_txrx_addr_ccc = target_addres ;

                    if (i_tx_mode_done) begin 
                        next_state = PARITY_CMD ;
                    end
                    else begin 
                        next_state = SECOND_CMD_BYTE ;
                    end

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
                end 
            end

            PARITY_CMD : begin 
                o_tx_en   = 1'b1 ; 
                o_tx_mode = parity_calc ;

                if (i_tx_mode_done) begin 
                    next_state   = PRE_FIRST_DATA_ONE ;
                    //o_frmcnt_en  = 1'b1 ;
                end
                else begin 
                    next_state = PARITY_CMD ;
                end

                // erorr state condition is remaining 

            end


            PRE_FIRST_DATA_ONE : begin // should be 10 to mean ACK ,    and 11 is NACK
            
                o_tx_en   = 1'b1 ;
                o_tx_mode = one ;
                o_rx_en   = 1'b0 ;

                if (i_tx_mode_done) begin
                    next_state = PRE_FIRST_DATA_TWO ;
                    //o_rx_en    = 1'b1 ;
                    //o_rx_mode  = preamble_rx_mode ;
                end
                else begin 
                    next_state = PRE_FIRST_DATA_ONE ;
                end 
            
            end 

            PRE_FIRST_DATA_TWO : begin 
                
                o_rx_en   = 1'b1 ;
                o_rx_mode = preamble_rx_mode ;

                if (i_rx_mode_done && !i_rx_pre && first_time) begin
                    next_state = CCC_BYTE ;
                    o_tx_en      = 1'b1 ;
                    o_tx_mode    = serializing_byte_port ;
                    o_txrx_addr_ccc = i_regf_CMD ;
                end

                else if (i_rx_mode_done && !i_rx_pre && !first_time) begin 
                
                    if (!i_regf_CMD_ATTR[0] && !i_regf_RnW) begin              // if regular command discriptor  (but long write) not supported cuurently but it's okk
                        o_tx_mode    = serializing_byte_regf ;
                        o_tx_en   = 1'b1 ;
                        o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 8 to point to the ninth location 
                        o_regf_wr_en = 1'b1 ;                
                    end
                    else if (!i_regf_CMD_ATTR[0] && i_regf_RnW) begin              // if Read & Regular command discriptor  
                        o_tx_en   = 1'b0 ;
                        o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 8 to point to the ninth location                 
                    end

                    else begin // if immediate
                        o_tx_en      = 1'b1 ;
                                                      
                        if (Defining_byte) begin 
                            o_regf_addr = first_location + immediate_counter + 1  ; // for 8 bit width Regfile .. point to sixth location
                            o_tx_mode   = serializing_byte_regf ;          // as first byte in the third location will contain the Defining Byte
                        end 
                        else begin 
                            o_regf_addr = first_location + immediate_counter ;        // for 8 bit width Regfile .. point to fourth location
                            o_tx_mode   = serializing_byte_regf ; 
                        end 
                    end

                    next_state = FIRST_DATA_BYTE ;
                end 

                else if (i_rx_mode_done && i_rx_pre) begin 
                    o_tx_en           = 1'b0 ;
                    next_state        = ERROR ;
                    o_regf_ERR_STATUS = NACK ;
                end 

                else begin 
                    next_state = PRE_FIRST_DATA_TWO ;
                end 

            end 


            CCC_BYTE : begin    // contains CCC value

                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_port ;
                o_txrx_addr_ccc = i_regf_CMD ;

                if (i_tx_mode_done && Defining_byte) begin   // if a defining byte exists
                    next_state = DEFINING_BYTE ;
                end
                else if (i_tx_mode_done && !Defining_byte) begin   
                    next_state = ZEROS ;
                end 
                else begin 
                    next_state = CCC_BYTE ;
                end

            end

            DEFINING_BYTE : begin    // contains definaing byte if exist
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_regf ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location + 4 ;                 // fifth location (8 bits width)
                o_frmcnt_en  = 1'b1 ;

                if (i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;
                end
                else begin 
                    next_state = DEFINING_BYTE ;
                end  
            end

            ZEROS : begin                               // eight zeros fixed at regfile (e.g location 999)
                o_tx_en      = 1'b1 ;
                o_tx_mode    = serializing_byte_regf ; 
                o_regf_rd_en = 1'b1 ;
                o_regf_addr  = first_location - 1  ;

                // new (instead of just o_frmcnt_en  = 1'b1 ;)
                if (Direct_Broadcast_n_del && first_time) begin 
                    o_frmcnt_en  = 1'b0 ;
                end
                else begin 
                    o_frmcnt_en  = 1'b1 ;
                end  
                //////////////////////////////////////////////////////
                if (i_frmcnt_last_frame) begin 
                    o_engine_odd = 1'b1 ; 
                end 
                else begin 
                    o_engine_odd = 1'b0 ; 
                end 

                if (i_tx_mode_done) begin   
                    next_state = PARITY_DATA ;

                end
                else begin 
                    next_state = ZEROS ;
                end

                // erorr state condition is remaining   
            end

            PARITY_DATA : begin // parity state any Data word
                if (!i_regf_RnW || first_time) begin // write 
                    o_tx_en   = 1'b1 ;
                    o_tx_mode = parity_calc ;
                    if  (i_tx_mode_done) begin // if broadcast

                        if (i_frmcnt_last_frame || (Direct_Broadcast_n_del & first_time)) begin  // crc state only in case of Direct or in case of last data 
                            next_state = PRE_CMD ; // BEGINING OF CRC 
                        end 
                        else begin 
                            next_state = PRE_DATA_ONE ; // not last byte then continue sending/recieving repeated data 
                        end 
                    end

                    else begin 
                        next_state = PARITY_DATA ;
                    end
                end 
                else begin // read 
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = parity_check ;
                    if  (i_rx_mode_done && !i_rx_error) begin 

                        if (i_frmcnt_last_frame || Direct_Broadcast_n_del) begin  // crc state only in case of Direct or in case of last data 
                            next_state = PRE_CRC_TARGET ; // 
                        end 
                        else begin 
                            next_state = PRE_DATA_ONE ; // not last byte then continue sending/recieving repeated data 

                        end 
                    end

                    else if (i_rx_mode_done && i_rx_error) begin 
                        next_state = ERROR ;
                        o_regf_ERR_STATUS = PARITY_ERR ;
                    end 

                    else begin 
                        next_state = PARITY_DATA ;
                    end
                end 
            end

            PRE_DATA_ONE : begin  //  11  means ok continue , and 10 to be aborted 
                if (!i_regf_RnW) begin // write 
                    o_tx_en   = 1'b1 ;
                    o_tx_mode = one ;
                    o_rx_en   = 1'b0 ;

                    if (i_tx_mode_done) begin
                        next_state = PRE_DATA_TWO ;
                        //o_rx_en  = 1'b1 ;
                        //o_rx_mode = preamble_rx_mode ;
                    end
                    else begin 
                        next_state = PRE_DATA_ONE ;
                    end 
                end 

                else begin 
                    o_tx_en   = 1'b0 ;
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = preamble_rx_mode ;
                    
                    if (i_rx_mode_done && i_rx_pre) begin
                        next_state = PRE_DATA_TWO ;
                        o_rx_mode  = preamble_rx_mode ;
                    end
                    else if (i_rx_mode_done && !i_rx_pre) begin
                        next_state = ERROR ;
                        o_regf_ERR_STATUS  = FRAME ;
                    end
                    else begin 
                        next_state = PRE_DATA_ONE ;
                    end 
                end 
            end 

            PRE_DATA_TWO : begin  //  11  means ok continue , and 10 to be aborted 
                if (!i_regf_RnW) begin // write
                    o_tx_en   = 1'b0 ;
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = preamble_rx_mode ;

                    if (i_rx_mode_done && i_rx_pre) begin  // ack by target
                        next_state = FIRST_DATA_BYTE ;
                    ////////////////////////////////// new ////////////////////////////////
                        o_tx_en      = 1'b1 ;
                        o_regf_rd_en = 1'b1 ;
                        if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                            o_tx_mode    = serializing_byte_regf ;
                            o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 8 to point to the ninth location 
                        end 
                        else begin                                  // if immediate
                            if (Defining_byte) begin 
                                o_regf_addr = first_location + immediate_counter + 1  ; // for 8 bit width Regfile .. point to sixth location
    
                                o_tx_mode   = serializing_byte_regf ;          // as first byte in the third location will contain the Defining Byte
                            end 
                            else begin 
                                o_regf_addr = first_location + immediate_counter ;        // for 8 bit width Regfile .. point to fourth location
                                o_tx_mode   = serializing_byte_regf ; 
                            end 
                        end 
                    //////////////////////////////////////////////////////////////////////
                    end

                    else if (i_rx_mode_done && !i_rx_pre) begin // abort by target
                        next_state        = ERROR ;
                        o_regf_ERR_STATUS = T_ABORTED ;
                    end 

                    else begin 
                        next_state = PRE_DATA_TWO ;
                    end 
                end 
                else begin 
                    // tx signals 
                    o_tx_en   = 1'b1 ;
                    if (controller_abort) begin 
                        o_tx_mode = zero ;
                    end 
                    else begin 
                        o_tx_mode = one ;                   // open drain
                        //o_sdahand_pp_od = open drain ; 
                    end 

                    // rx signals 
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = preamble_rx_mode ;

                    if ((i_rx_mode_done || i_tx_mode_done) && i_rx_pre) begin  // the coming is data still  in this case we may need the bit count number ?
                        next_state = FIRST_DATA_BYTE ;
                    end

                    else if (i_rx_mode_done && !i_rx_pre) begin // abort by target and crc is following
                        next_state        = C_TOKEN_STATE ;
                        o_regf_ERR_STATUS = T_ABORTED ;
                    end 

                    else begin 
                        next_state = PRE_DATA_TWO ;
                    end
                end 
                
            end 


            FIRST_DATA_BYTE : begin    // contains first repeated data byte
                if (!i_regf_RnW) begin  // write operation 
                    o_tx_en      = 1'b1 ;
                    o_regf_rd_en = 1'b1 ;
                    if (!i_regf_CMD_ATTR[0]) begin              // if regular command discriptor  
                        o_tx_mode    = serializing_byte_regf ;
                        o_regf_addr  = first_location + regular_counter ; // regular counter starts with value 8 to point to the ninth location 
                    end 
                    else begin                                  // if immediate
                        if (Defining_byte) begin 
                            o_regf_addr = first_location + immediate_counter + 1  ; // for 8 bit width Regfile .. point to sixth location
    
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
                //////////////// new 3/5/2024 
                if (i_frmcnt_last_frame) begin 
                    o_engine_odd = 1'b1 ; 
                end 
                else begin 
                    o_engine_odd = 1'b0 ; 
                end 
                ///////////////////////////////////////// 
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
                if (i_tx_mode_done && i_frmcnt_last_frame) begin  // to handle odd number of bytes in both regular and immediate
                    next_state   = ZEROS ; 
                    //o_engine_odd = 1'b1 ;            // to be put in the response discreptor      
                end

                //// new 3/5/2024
                else if (i_rx_mode_done && i_frmcnt_last_frame) begin 
                    next_state = SECOND_DATA_BYTE ; 
                    //immediate_counter = immediate_counter + 1 ;  there can't be immediate Transfer Command Discriptor with direct get 
                    regular_counter   = regular_counter + 1 ;
                end 
                /////////////////////

                else if ((i_rx_mode_done | i_tx_mode_done) && !i_frmcnt_last_frame) begin  
                    next_state = SECOND_DATA_BYTE ; 
                    immediate_counter = immediate_counter + 1 ;
                    regular_counter   = regular_counter + 1 ;
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
                    if (i_tx_mode_done) begin 
                        next_state = PARITY_DATA ; 
                        if (i_frmcnt_last_frame) begin 
                            // no need to put conditions , immediated and regular can't happen together
                            immediate_counter = immediate_counter ;
                            regular_counter   = regular_counter   ;
                        end 
                        else begin 
                            // no need to put conditions , immediated and regular can't happen together
                            immediate_counter = immediate_counter + 1 ;
                            regular_counter   = regular_counter   + 1 ;
                        end        
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
                    if (i_rx_mode_done) begin   
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
        
            C_TOKEN_STATE : begin 
                o_bitcnt_en        = 1'b0 ;
                if (!i_regf_RnW || first_time) begin // write 
                    o_tx_en   = 1'b1 ;
                    o_tx_mode = c_token_CRC ;

                    if (i_tx_mode_done) begin 
                        next_state = CRC_CHECKSUM_STATE ; // 6 bits (5 checksum + 1 high to prepare for restart or exit)
                    end 
                    else begin 
                        next_state = C_TOKEN_STATE ;
                    end
                end 
                else begin // read 
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = check_c_token_CRC ;
                    if (i_rx_error) begin 
                        next_state = ERROR ; 
                        o_regf_ERR_STATUS = CRC_ERR ;
                    end
                    else if (i_rx_mode_done && !i_rx_error) begin 
                        next_state = CRC_CHECKSUM_STATE ; // 5 bits checksum
                    end 
                    
                    else begin 
                        next_state = C_TOKEN_STATE ;
                    end
                end  
            end 

            CRC_CHECKSUM_STATE : begin 
                o_bitcnt_en        = 1'b0 ;
                if (!i_regf_RnW || first_time) begin  // write 
                    o_tx_en   = 1'b1 ;
                    o_tx_mode = value_CRC ;
                    if (i_tx_mode_done) begin 
                        //////////////////////////// new /////////////////////////////////////////////
                        if (!Direct_Broadcast_n_del && i_regf_TOC) begin 
                            next_state    = EXIT_PATTERN ;
                            first_time    = 1'b0 ;
                            o_sclstall_en    = 1'b1 ;
                            o_sclstall_code  = exit_pattern_stall ;
                        end
                        else if (!Direct_Broadcast_n_del && !i_regf_TOC) begin 
                            next_state = RESTART_PATTERN ;
                            o_sclstall_en   = 1'b1 ;
                            o_sclstall_code = restart_pattern_stall ;
                            first_time      = 1'b0 ;
                        end  
                        else if (Direct_Broadcast_n_del && first_time) begin 
                            next_state = RESTART_PATTERN ;
                            o_sclstall_en   = 1'b1 ;
                            o_sclstall_code = restart_pattern_stall ;
                            first_time    = 1'b0 ;
                        end
                        else if (Direct_Broadcast_n_del && !first_time) begin 
                            if (!i_regf_TOC) begin 
                                next_state = RESTART_PATTERN ;
                                o_sclstall_en   = 1'b1 ;
                                o_sclstall_code = restart_pattern_stall ;
                            end 
                            else begin
                                next_state      = EXIT_PATTERN ;
                                o_sclstall_en   = 1'b1 ;
                                o_sclstall_code = exit_pattern_stall ;
                            end  
                        end
                    ////////////////////////////////////////////////////////////////////////////////////
                    end
                    else begin 
                        next_state = CRC_CHECKSUM_STATE ;
                    end 
                end 
                else begin 
                    o_rx_en   = 1'b1 ;
                    o_rx_mode = check_value_CRC ;
                    if (i_rx_mode_done && !i_rx_error) begin 
                        if (i_regf_TOC) begin 
                            next_state    = EXIT_PATTERN ;
                            first_time    = 1'b0 ;
                            o_tx_mode     = exit_pattern ;
                            o_tx_en       = 1'b1 ;
                            o_sclstall_en    = 1'b1 ;
                            o_sclstall_code  = exit_pattern_stall ;
                        end 
                        else begin  
                            next_state      = RESTART_PATTERN_SPECIAL ;
                            o_sclstall_en   = 1'b1 ;
                            o_sclstall_code = restart_pattern_stall_special ;
                            first_time      = 1'b0 ;
                            o_tx_mode       = restart_pattern ;
                            o_tx_en         = 1'b1 ;
                        end
                    end
                    else begin 
                        next_state = CRC_CHECKSUM_STATE ;
                    end 
                end  
            end 


            RESTART_PATTERN_SPECIAL : begin 
                o_bitcnt_en        = 1'b0 ;
                // access timer and staller and tx to perform restart pattern 
                o_tx_en         = 1'b1 ;
                o_tx_mode       = restart_pattern ;
                o_sclstall_en   = 1'b1 ;
                o_sclstall_code = restart_pattern_stall_special ;

                if (i_sclstall_stall_done && i_tx_mode_done && i_frmcnt_last_frame) begin 
                    next_state = FINISH ;
                end 
                else if (i_sclstall_stall_done && i_tx_mode_done && !i_frmcnt_last_frame) begin 
                    next_state = PRE_CMD ;
                end 
                else begin 
                    next_state = RESTART_PATTERN_SPECIAL ;
                end
            end 


            RESTART_PATTERN : begin 
                o_bitcnt_en        = 1'b0 ;
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
                o_tx_en          = 1'b1 ;
                o_tx_mode        = exit_pattern ;
                o_sclstall_en    = 1'b1 ;
                o_sclstall_code  = exit_pattern_stall ;
                o_bitcnt_err_rst = 1'b0 ;
                o_bitcnt_en      = 1'b0 ;

                if (i_tx_mode_done) begin 
                    next_state = FINISH ;
                end  
                else begin 
                    next_state = EXIT_PATTERN ;
                end
            end



 
            ERROR : begin      // controller error state 
                o_bitcnt_err_rst = 1'b1 ; // active hight rst to count specially for error state

                o_tx_en   = 1'b0 ;
                if(i_bitcnt_number == 37) begin 
                    next_state      = EXIT_PATTERN ; // may issue exit or restart pattern .. but conditions ?
                    o_tx_en         = 1'b1 ; 
                    o_tx_mode       = exit_pattern ;
                    o_sclstall_en   = 1'b1 ;
                    o_sclstall_code = exit_pattern_stall ;
                end 
                else begin 
                    next_state = ERROR ;
                end 

            end 

            

            FINISH : begin 
                
                first_time        = 1'b1 ;   // flag to help to differentiate between the direct and broadcast with assistance of Direct_Braodcast_n flag 
                o_bitcnt_en       = 1'b0 ;
                regular_counter   =  'd8 ;   // data starts from ninth location 1008
                immediate_counter =  'd4 ;   // data starts from fifth location 1004 
                o_engine_odd      = 1'b0 ;
                controller_abort  = 1'b0 ;
                o_engine_done     = 1'b1 ;
                o_frmcnt_en       = 1'b0 ;
                o_regf_ERR_STATUS = SUCCESS ;
                next_state        = IDLE ;

            end 
        endcase
    end
endmodule 
//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors: Yaseen Salah , Youssef Noeman
// Revision: Youssef Noaman , Yaseen Salah , Nour Eldeen Samir 
//
// Version : 1.0
//
// Create Date:  21:33:27 10/02/2023  
// Design Name:  bits_counter
// Module Name:  bits_counter
//
//==================================================================================
//
//  STATEMENT OF USE
//
//  This information contains confidential and proprietary information of MIXEL.
//  No part of this information may be reproduced, transmitted, transcribed,
//  stored in a retrieval system, or translated into any human or computer
//  language, in any form or by any means, electronic, mechanical, magnetic,
//  optical, chemical, manual, or otherwise, without the prior written permission
//  of MIXEL.  This information was prepared for Garduation Project purpose and is for
//  use by MIXEL Engineers only.  MIXEL and ASU 2023 GP reserves the right 
//  to make changes in the information at any time and without notice.
//
//==================================================================================
//////////////////////////////////////////////////////////////////////////////////

`default_nettype none
module bits_counter(
    input  wire       i_cnt_en              ,  
    input  wire       i_ctrl_rx_cnt_en      , // controller is in DATA IN state 
    input  wire       i_rst_n               ,
    input  wire       i_bits_cnt_clk        ,
    input  wire       i_sdr_ctrl_pp_od      , //UNUSED
    input  wire       i_scl_pos_edge        ,  
    input  wire       i_scl_neg_edge        ,  
    input  wire       i_bits_cnt_regf_rx_tx ,  // 0 for TX , 1 for RX
    output reg        o_cnt_done            ,
    output wire [2:0] o_cnt_bit_count
    );

// INTERNAL SIGNALS 
    reg [2:0] cnt_bit_count ;
    
// OUTPUT 
    assign o_cnt_bit_count = cnt_bit_count;
    
// COUNTER CORE
always @ (posedge i_bits_cnt_clk or negedge i_rst_n)
    begin : counter
        if (!i_rst_n)
            begin 
                cnt_bit_count <= 3'b111 ;
                o_cnt_done    <= 1'b0   ;    
            end
            
        else if (i_cnt_en)
            begin
                if(i_bits_cnt_regf_rx_tx && i_ctrl_rx_cnt_en) // RX condition 
                    begin
                        if (i_scl_neg_edge) 
                            begin 
                                if (!cnt_bit_count )
                                     begin
                                        cnt_bit_count <= 3'b111 ;
                                        o_cnt_done    <= 1'b1   ;    
                                     end
                                else    
                                     begin               
                                        cnt_bit_count <= cnt_bit_count - 1'd1 ;
                                        o_cnt_done    <= 1'b0                 ;
                                     end
                            end
                    end
                else                    // TX condition 
                    begin
                        if (i_scl_pos_edge) 
                            begin 
                                if (!cnt_bit_count )
                                     begin
                                        cnt_bit_count <= 3'b111 ;
                                        o_cnt_done    <= 1'b1   ;    
                                     end
                                else    
                                     begin               
                                        cnt_bit_count <= cnt_bit_count - 1'd1 ;
                                        o_cnt_done    <= 1'b0                 ;
                                     end
                            end
                    end        
            end
        else
              begin
                  cnt_bit_count <= 3'b111 ;
                  o_cnt_done    <= 1'b0   ;    
              end


    end 

endmodule
`default_nettype wire
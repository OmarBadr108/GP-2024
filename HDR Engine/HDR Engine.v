/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Fatma Saad Abdallah
 
 Revision:   

 Version : 1.0

 Create Date: 18/2/2024
 Design Name:  HDR_ENGINE
 Module Name:  hdr_engine

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
module hdr_engine (
    input   wire            i_sys_clk                             ,
    input   wire            i_sys_rst_n                           ,
    input   wire            i_i3cengine_hdrengine_en              , 
    input   wire            i_ccc_done                            ,
    input   wire            i_hdr_mode_done                       ,
    input   wire            i_TOC                                 , //term of completion if 0 restart/ 1 exit needed for exit
    input   wire            i_CP                                  , // Cmnd present=1 if CCC 0 for Normal Transcation
    //input   wire  [3:0]     i_TID                                 , //Transaction id for each CCC
    input   wire  [2:0]     i_MODE                                ,
    //to_blocks
    output  reg             o_i3cengine_hdrengine_done            ,
    output  reg             o_hdrmode_en                          ,
    output  reg             o_ccc_en                              
    //config
    //output  reg   [3:0]     o_TID                                 ,
    //output  reg   [7:0]     o_ERR_STATUS                          ,
    //output  reg   [15:0]    o_DATA_LENGTH                         

    );

//--------------------------------- main ------------------------------------------------

always @(posedge i_sys_clk or negedge i_sys_clk or negedge i_sys_rst_n ) 
  begin: hdr_engine_fsm
    if (!i_sys_rst_n) 
        begin
            o_i3cengine_hdrengine_done      <= 1'b0   ;
            o_hdrmode_en                    <= 1'b0   ;
            o_ccc_en                        <= 1'b0   ;
            //config
            //o_TID                           <= 4'b0   ;
            //o_ERR_STATUS                    <= 8'b0   ;
            //o_DATA_LENGTH                   <= 16'b0  ;

            //state                           <= IDLE;
        end

    else
        begin
            if (i_i3cengine_hdrengine_en) 
            begin
                if(i_CP) begin
                    o_ccc_en        <= 1'b1 ;
                    if((i_TOC && i_ccc_done)||(i_MODE != 'd6)) begin
                        o_ccc_en    <= 1'b0 ;
                        o_i3cengine_hdrengine_done      <= 1'b1 ;
                      end
                    else
                        o_i3cengine_hdrengine_done      <= 1'b0 ;
                end
                else if (!i_CP) 
                begin
                    o_hdrmode_en        <= 1'b1 ;
                    if((i_TOC && i_hdr_mode_done)||(i_MODE != 'd6)) begin
                        o_hdrmode_en    <= 1'b0 ;
                        o_i3cengine_hdrengine_done      <= 1'b1 ;
                      end
                    else
                        o_i3cengine_hdrengine_done      <= 1'b0 ;
                end
                else begin
                  o_i3cengine_hdrengine_done      <= 1'b0 ;
                  o_ccc_en                        <= 1'b0  ;
                  o_hdrmode_en                    <= 1'b0  ; 
                end
            end
            else
                begin
                    o_i3cengine_hdrengine_done      <= 1'b0  ;
                    o_ccc_en                        <= 1'b0  ;
                    o_hdrmode_en                    <= 1'b0  ;

                end

            
        end
end 
endmodule

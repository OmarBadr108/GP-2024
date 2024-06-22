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
    input   wire            i_ddr_mode_done                       ,
    input   wire            i_TOC                                 , //term of completion if 0 restart/ 1 exit needed for exit
    input   wire            i_CP                                  , // Cmnd present=1 if CCC 0 for Normal Transcation
    input   wire  [2:0]     i_MODE                                ,
    //input   wire  [3:0]     i_TID                               ,
    //to_blocks
    output  reg             o_i3cengine_hdrengine_done            ,
    output  reg             o_ddrmode_en                          ,
    output  reg             o_ccc_en                              ,

    output  reg   [11:0]     o_regf_addr_special                  ,
    
    output  reg             o_tx_en_sel                           ,
    output  reg             o_rx_en_sel                           ,
    output  reg             o_tx_mode_sel                         ,
    output  reg             o_rx_mode_sel                         ,
    output  reg             o_regf_rd_en_sel                      ,
    output  reg             o_regf_wr_en_sel                      ,
    output  reg             o_regf_addr_sel                       ,
    output  reg             o_scl_pp_od_sel                       ,
    output  reg             o_bit_cnt_en_sel                      ,
    output  reg             o_frm_cnt_en_sel                      ,
    output  reg             o_sdahand_pp_od_sel                    

    //output  reg  [3:0]     o_TID

    );
/////////////parameters////////////
localparam  IDLE          = 2'b00;
localparam  CCC           = 2'b01;
localparam  DDR_MODE      = 2'b10;

reg [1:0] current_state, next_state;
reg ccc_done;
reg i_CP_temp;
reg i_TOC_temp;
reg [2:0] i_MODE_temp;


/////////////Mux Selection Parameters///////////////
localparam DDR_SEL=1'b0;
localparam CCC_SEL=1'b1;

//--------------------------------- main ------------------------------------------------

always @(posedge i_sys_clk or negedge i_sys_rst_n ) 
  begin: hdr_engine_fsm
    if (!i_sys_rst_n) 
        begin
            o_i3cengine_hdrengine_done      <= 1'b0   ;
            o_ddrmode_en                    <= 1'b0   ;
            o_ccc_en                        <= 1'b0   ;
            o_regf_addr_special             <= 12'd1000 ;
            i_CP_temp   <= 1'b0;
            i_TOC_temp    <=1'b0;
            i_MODE_temp   <='d6;
            //current_state                   <= IDLE ;
            next_state                   <= IDLE ;
        end

    else 
      begin
      o_regf_addr_special             <= 12'd1000 ;
        //current_state <= next_state;
        case (next_state)    //case (current_state)

          IDLE : begin

            // register the configuration values from regfile
              i_CP_temp   <= i_CP;
              i_TOC_temp  <= i_TOC;
              i_MODE_temp <= i_MODE;
            if (i_i3cengine_hdrengine_en) 
             begin


                      if(i_CP_temp) 
                        begin
                             o_ccc_en        <= 1'b1 ;
                             next_state      <= CCC ;
        
                             // mux selectors         
                             o_tx_en_sel            <=CCC_SEL;  
                             o_rx_en_sel            <=CCC_SEL;
                             o_tx_mode_sel          <=CCC_SEL;
                             o_rx_mode_sel          <=CCC_SEL;
                             o_regf_rd_en_sel       <=CCC_SEL;
                             o_regf_wr_en_sel       <=CCC_SEL;
                             o_regf_addr_sel        <=CCC_SEL;
                             o_scl_pp_od_sel        <=CCC_SEL;
                             o_bit_cnt_en_sel       <=CCC_SEL;
                             o_frm_cnt_en_sel       <=CCC_SEL;
                             o_sdahand_pp_od_sel    <=CCC_SEL;    
                         end
                      else 
                        begin
                              o_ddrmode_en      <= 1'b1 ;
                              next_state        <= DDR_MODE ;
                             o_tx_en_sel            <=DDR_SEL;  
                             o_rx_en_sel            <=DDR_SEL;
                             o_tx_mode_sel          <=DDR_SEL;
                             o_rx_mode_sel          <=DDR_SEL;
                             o_regf_rd_en_sel       <=DDR_SEL;
                             o_regf_wr_en_sel       <=DDR_SEL;
                             o_regf_addr_sel        <=DDR_SEL;
                             o_scl_pp_od_sel        <=DDR_SEL;
                             o_bit_cnt_en_sel       <=DDR_SEL;
                             o_frm_cnt_en_sel       <=DDR_SEL;
                             o_sdahand_pp_od_sel    <=DDR_SEL;  
        
                        end
          end

          else
              begin
                o_i3cengine_hdrengine_done      <= 1'b0   ;
                o_ddrmode_en                    <= 1'b0   ;
                o_ccc_en                        <= 1'b0   ;
                next_state                      <= IDLE;  
              end

          end 

          CCC : begin
            i_CP_temp   <= i_CP;
if (i_i3cengine_hdrengine_en) begin

          
            if((i_TOC_temp && i_ccc_done)||(i_MODE_temp != 'd6)) begin     // ||(i_MODE != 'd6) assuming mode will not be changed unless an exit pattern was sent before it. -laila
                  o_ccc_en    <= 1'b0 ;
                  o_i3cengine_hdrengine_done      <= 1'b1 ;
                  next_state <= IDLE;             
                  ///tid puts on output when the command is done


            end
            else if ((!i_TOC_temp && i_ccc_done) && (i_MODE_temp == 'd6)) begin
              ccc_done                      <= 1'b0 ; //******signal 3mltha 3shan a3rf arg3 ll ddrmode*//////
              o_ccc_en                      <= 1'b0 ;
              o_regf_addr_special           <= 12'd1000;
              o_i3cengine_hdrengine_done    <= 1'b0 ;
              ///tid puts on output when the command is done
              
            // register the configuration values from regfile
              
              i_TOC_temp  <= i_TOC;
              i_MODE_temp <= i_MODE;

                  if(!i_CP_temp) 
                  begin
                    ccc_done   <= 1'b1 ;
                    o_regf_addr_special <= 12'd450; //go to special address to get dummy value
                    o_ccc_en   <= 1'b1 ;
                    next_state <= CCC ; ////********lma yru7 y3ml al dummy hwdeh ddr azay*******//////////
                  end
                  else
                    begin
                      o_ccc_en                      <= 1'b1 ;
                      o_regf_addr_special           <= 12'd1000;
                      next_state                    <= CCC ;    
                    end

                  ////****/////
                  if(i_ccc_done && ccc_done && !i_CP_temp ) begin
                    o_regf_addr_special           <= 12'd1000;
                    o_ccc_en   <= 1'b0 ;
                    o_ddrmode_en <= 1'b1 ;
                    next_state   <= DDR_MODE ;
                     o_tx_en_sel            <=DDR_SEL;  
                     o_rx_en_sel            <=DDR_SEL;
                     o_tx_mode_sel          <=DDR_SEL;
                     o_rx_mode_sel          <=DDR_SEL;
                     o_regf_rd_en_sel       <=DDR_SEL;
                     o_regf_wr_en_sel       <=DDR_SEL;
                     o_regf_addr_sel        <=DDR_SEL;
                     o_scl_pp_od_sel        <=DDR_SEL;
                     o_bit_cnt_en_sel       <=DDR_SEL;
                     o_frm_cnt_en_sel       <=DDR_SEL;
                     o_sdahand_pp_od_sel    <=DDR_SEL;   
                  end
                  else begin
                    next_state   <= CCC ;
                    o_tx_en_sel            <=CCC_SEL;  
                    o_rx_en_sel            <=CCC_SEL;
                    o_tx_mode_sel          <=CCC_SEL;
                    o_rx_mode_sel          <=CCC_SEL;
                    o_regf_rd_en_sel       <=CCC_SEL;
                    o_regf_wr_en_sel       <=CCC_SEL;
                    o_regf_addr_sel        <=CCC_SEL;
                    o_scl_pp_od_sel        <=CCC_SEL;
                    o_bit_cnt_en_sel       <=CCC_SEL;
                    o_frm_cnt_en_sel       <=CCC_SEL;
                    o_sdahand_pp_od_sel    <=CCC_SEL;
                    end  
            end
            else
               begin
                  o_i3cengine_hdrengine_done      <= 1'b0 ;
                  o_ccc_en                      <= 1'b1 ;
                end
                  
          
          
end

else
                next_state                      <= IDLE;
               /* o_i3cengine_hdrengine_done      <= 1'b0   ;
                o_ddrmode_en                    <= 1'b0   ;
                o_ccc_en                        <= 1'b0   ;
*/

end

          DDR_MODE : begin
            i_CP_temp   <= i_CP;
if (i_i3cengine_hdrengine_en) begin


          
            if ((i_TOC_temp && i_ddr_mode_done)||(i_MODE_temp != 'd6)) begin
              o_ddrmode_en    <= 1'b0 ;
              o_i3cengine_hdrengine_done      <= 1'b1 ;
              next_state <= IDLE;
              //tid puts on output when it is done
            end
            else if ((!i_TOC_temp && i_ddr_mode_done) && (i_MODE_temp == 'd6)) begin
              o_ddrmode_en    <= 1'b0 ;
              o_i3cengine_hdrengine_done    <= 1'b0 ;
              //tid puts on output when it is done

          // register the new configuration values from regfile
              
              i_TOC_temp  <= i_TOC;
              i_MODE_temp <= i_MODE;

                  if (!i_CP_temp) begin
                    o_ddrmode_en <= 1'b1 ;
                    next_state   <= DDR_MODE ;
                     o_tx_en_sel            <=DDR_SEL;  
                     o_rx_en_sel            <=DDR_SEL;
                     o_tx_mode_sel          <=DDR_SEL;
                     o_rx_mode_sel          <=DDR_SEL;
                     o_regf_rd_en_sel       <=DDR_SEL;
                     o_regf_wr_en_sel       <=DDR_SEL;
                     o_regf_addr_sel        <=DDR_SEL;
                     o_scl_pp_od_sel        <=DDR_SEL;
                     o_bit_cnt_en_sel       <=DDR_SEL;
                     o_frm_cnt_en_sel       <=DDR_SEL;
                     o_sdahand_pp_od_sel    <=DDR_SEL;  
                  end
                  else begin
                    o_ccc_en <= 1'b1 ;
                    next_state <= CCC ;
                     o_tx_en_sel            <=CCC_SEL;  
                     o_rx_en_sel            <=CCC_SEL;
                     o_tx_mode_sel          <=CCC_SEL;
                     o_rx_mode_sel          <=CCC_SEL;
                     o_regf_rd_en_sel       <=CCC_SEL;
                     o_regf_wr_en_sel       <=CCC_SEL;
                     o_regf_addr_sel        <=CCC_SEL;
                     o_scl_pp_od_sel        <=CCC_SEL;
                     o_bit_cnt_en_sel       <=CCC_SEL;
                     o_frm_cnt_en_sel       <=CCC_SEL;
                     o_sdahand_pp_od_sel    <=CCC_SEL;  
                  end
            end
            else
              begin
                o_i3cengine_hdrengine_done      <= 1'b0 ;
                o_ddrmode_en                    <= 1'b1   ;
              end
          end
else begin

                  o_i3cengine_hdrengine_done      <= 1'b0   ;
                o_ddrmode_en                    <= 1'b0   ;
                o_ccc_en                        <= 1'b0   ;
                next_state                      <= IDLE; 
end

end
        endcase
      end
      




end 
endmodule


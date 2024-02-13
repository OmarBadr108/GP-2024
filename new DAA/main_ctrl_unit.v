//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Youssef Essam , Zyad Sobhy
// Revision: 
//
// Version : 1.0
// 
// Create Date:  7:46 PM     23/2/2023 
// Design Name:  I3C controller
// Module Name:  main_ctrl_unit
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
////////////////////////////////////////////////////////////////////////////////////

`default_nettype none

module main_ctrl_unit (
input  	wire          i_mcu_clk                ,
input  	wire          i_mcu_rst_n              ,
input  	wire          i_mcu_en                 ,
input  	wire          i_daa_done               ,
input  	wire          i_ibi_done               ,
input  	wire          i_ibi_en_tb              , //for testing to be removed 
input  	wire          i_hj_done                ,
input  	wire          i_sc_done                ,
input  	wire          i_sdr_done               ,
input   wire       i_mcu_ibi_payload_en        ,
input   wire       i_mcu_sdr_payload_done      , 


output   reg       o_mcu_ibi_payload_done      ,
output  reg           o_daa_en                 ,
output  reg           o_ibi_en                 ,
output  reg           o_hj_en                  ,
output  reg           o_sc_en                  ,
output  reg           o_sdr_en                 ,
output  reg   [2:0]   o_regf_rd_en_mux_sel           ,
output  reg   [2:0]   o_regf_wr_en_mux_sel           ,
output  reg   [2:0]   o_regf_rd_address_mux_sel      ,
output  reg   [2:0]   o_scl_pp_od_mux_sel            ,
output  reg   [2:0]   o_rx_en_mux_sel                ,
output  reg   [2:0]   o_tx_en_mux_sel                ,
output  reg   [2:0]   o_tx_mode_mux_sel              ,
output  reg   [2:0]   o_rx_mode_mux_sel              ,
output  reg   [2:0]   o_cnt_en_mux_sel               ,
output  reg   [2:0]   fcnt_no_frms_mux_sel
);


//-------------------------------- states encoding in gray ----------------------------------------------

localparam IDLE     	       = 4'b0000 ; 
localparam DAA    		       = 4'b0001 ;
localparam HOT_JOIN            = 4'b0011 ;
localparam SDR_MODE     	   = 4'b0010 ;
localparam SEC_CONTROLLER      = 4'b0110 ;
localparam IBI                 = 4'b0111 ;

//--------------------------------- internal wires declaration ------------------------------------------

reg [3:0] state;


//----------------------------------Mux Selection Parameters------------------------------------------//
localparam SDR_SEL = 4'b0000;
localparam IBI_SEL = 4'b0001;
localparam HJ_SEL  = 4'b0010;
localparam DAA_SEL = 4'b0011;
localparam SC_SEL  = 4'b0100;



//--------------------------------- controller main fsm ---------------------------------------------------

always @(posedge i_mcu_clk or negedge i_mcu_rst_n) 
  begin: controller_main_fsm
    
    if (!i_mcu_rst_n) 
    	begin
    	     o_daa_en <= 1'b0;
             o_ibi_en <= 1'b0;
             o_hj_en  <= 1'b0;
             o_sc_en  <= 1'b0;
             o_sdr_en <= 1'b0;
             state <= IDLE; 
             o_ibi_en <= 1'b0;
    	end

    else
    	begin
    		case(state)
    		IDLE:
    		begin
    		if (i_ibi_en_tb)
    		  begin
    		      o_ibi_en <= 1'b1;
    		       state   <= IBI;
    		  end     
    		else   
    		      begin
    		        o_ibi_en <= 1'b0;  
    		        state   <= IDLE;
    		      end
    		end 
    		
    		SDR_MODE: begin
    		              o_regf_rd_en_mux_sel       <= SDR_SEL; 
                          o_regf_wr_en_mux_sel       <= SDR_SEL; 
                          o_regf_rd_address_mux_sel  <= SDR_SEL; 
                          o_scl_pp_od_mux_sel        <= SDR_SEL; 
                          o_rx_en_mux_sel            <= SDR_SEL; 
                          o_tx_en_mux_sel            <= SDR_SEL; 
                          o_tx_mode_mux_sel          <= SDR_SEL; 
                          o_rx_mode_mux_sel          <= SDR_SEL; 
                          o_cnt_en_mux_sel           <= SDR_SEL;
    		            if (i_mcu_sdr_payload_done)
    		              begin
    		                  state   <= IDLE;
    		              end
    		          end
    		
    		IBI:
    		   begin
    		   o_regf_rd_en_mux_sel       <= IBI_SEL;
               o_regf_wr_en_mux_sel       <= IBI_SEL;
               o_regf_rd_address_mux_sel  <= IBI_SEL;
               o_scl_pp_od_mux_sel        <= IBI_SEL;
               o_rx_en_mux_sel            <= IBI_SEL;
               o_tx_en_mux_sel            <= IBI_SEL;
               o_tx_mode_mux_sel          <= IBI_SEL;
               o_rx_mode_mux_sel          <= IBI_SEL;
               o_cnt_en_mux_sel           <= IBI_SEL;
    		   
    		   //for testing to be removed
    		   if (!i_ibi_en_tb)      
    		      begin
    		          state <= IDLE;
    		      end
    		   ////////////////////////////////
    		   
    		    if (i_mcu_ibi_payload_en)      
    		      begin
    		          state <= SDR_MODE;
    		      end
    		               
    		   end 
    		
    		
    		DAA:
    		    		begin
    		end 

    		HOT_JOIN:
    		    		begin
    		end 

    		SEC_CONTROLLER:    		begin
    		end 


        
    	endcase
    	end

  end


endmodule

`default_nettype wire
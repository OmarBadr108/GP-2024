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
input wire 		  i_exit_done ,
input wire		  i_restart_done ,
inpur wire 		  i_RnW ,
input wire [15:0] i_regf_MWL ,
input wire [15:0] i_regf_MRL ,
input wire [7:0]  i_CCC_value ,
input wire [7:0]  i_Def_byte ,
input wire        i_rx_error

output reg 		  o_tx_en ,
output reg [4:0]  o_tx_mode ,
output reg 		  o_rx_en ,
output reg [4:0]  o_rx_mode ,
output reg 		  o_engine_done ,
output reg [7:0]  o_regf_addr ,
output reg 		  o_regf_wr_en ,
output reg 		  o_regf_rd_en 



);


// internal signals 
reg [4:0] current_state , next_state ;




// Local Parameters of States
localparam [4:0] IDLE = 5'd0 ;
localparam [4:0] PRE_CMD = 5'd1 ;
localparam [4:0] CHECK_CCC = 5'd2 ;



//Local Parameters of TX modes
localparam [4:0] one_preamble = 5'd0 ;



//Local Parameters of RX modes
localparam [4:0] zero_preamble = 5'd0 ;
localparam [4:0] ccc_value = 5'd1 ;


///////////////////////////state transition ///////////////////////
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
    o_tx_mode          = 4'b0 ; 
    o_rx_en            = 1'b0 ; 
    o_rx_mode          = 4'b0 ; 
    o_regf_wr_en       = 1'b0 ;
    o_regf_rd_en       = 1'b0 ;
    o_regf_addr        = 8'b0 ;
    o_engine_done      = 1'b0 ;

        case (current_state)

        	IDLE : begin

 				if (i_engine_en) begin 
                    next_state = PRE_CMD ;
                    o_rx_en    = 1'b1 ; 
                    o_rx_mode  = zero_preamble ; 
                end
                else begin 
                    next_state = IDLE ;
                end 

            end 

			PRE_CMD : begin
                if (i_engine_en) begin 
                	if (i_rx_mode_done) begin //flag true when the data is 0 preamble
                		o_rx_en = 1'b0 ;
                		o_tx_en = 1'b1 ;
                		o_tx_mode = one_preamble ;
                		next_state = ACK ;
                	end
                	else
                		next_state = PRE_CMD ;
                else
                	next_state = IDLE ;
            end 
            ACK : begin
            	if (i_tx_mode_done) begin
            		o_tx_en = 1'b0 ;
            		o_rx_en = 1'b1 ;
            		o_rx_mode = ccc_value ;
            		next_state = CHECK_CCC ;
            	end
            	else
            		next_state = ACK ;

            end
            CHECK_CCC : begin
            	if (i_CCC_value== 0x00) begin //ENEC_BC
            		/* code */
            	end
            	else if (i_CCC_value== 0x01) begin //DISEC_BC
            		/* code */
            	end
            	else if (i_CCC_value== 0x80) begin //ENEC_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x81) begin //DISEC_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x80) begin //ENEC_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x09) begin //SETMWL_BC
            		/* code */
            	end
            	else if (i_CCC_value== 0x0A) begin //SETMRL_BC
            		/* code */
            	end
            	else if (i_CCC_value== 0x89) begin //SETMWL_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8B) begin //GETMWL_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8A) begin //SETMRL_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8C) begin //GETMRL_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x90) begin //GETSTATUS_Dir format 1
            		/* code */
            	end
            	else if (i_CCC_value== 0x2A) begin //RSTACT_BC
            		/* code */
            	end
            	else if (i_CCC_value== 0x9A) begin //RSTACT_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8D) begin //GETPID_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8E) begin //GETBCR_Dir
            		/* code */
            	end
            	else if (i_CCC_value== 0x8F) begin //GETDCR_Dir
            		/* code */
            	end
            	else
            		next_state = CHECK_CCC ;
            end 



//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Zyad Sobhi , Youssef Amr
// Revision: Yaseen Salah
//
// Version : 1.0
//
// Create Date:  3:32 PM     12/13/2022
// Design Name:  sda_handling
// Module Name:  sda_handling
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

module sda_handling(
  input   wire   i_handling_s_data     ,
	input   wire   i_handling_sel_pp_od  , 	//push-pull_open-drain: takes 1 when push-pull and 0 when open-drain
	input   wire   i_handling_pp_en      ,
	inout   wire   sda	                 ,
	output  wire   o_handling_s_data    );


//-- internal wires declaration -----------------------------------------------

	wire          open_drain_out ;
	wire          push_pull_out  ;
	reg           open_drain_in  ;
	reg           push_pull_in   ;
	wire          push_pull_enable ;

assign push_pull_enable = i_handling_pp_en && i_handling_sel_pp_od ; 

//-- SDA from PP/OD to Rx MUX ------------------------------------------------

assign o_handling_s_data = (i_handling_sel_pp_od )?  push_pull_out : open_drain_out ;


//-- SDA from Tx to PP/OD DEMUX -----------------------------------------------

always@(*)
  begin : demux_combo_logic
    if (i_handling_sel_pp_od)
      begin
        open_drain_in = 1'b1 ;  //--------- because it is active low
        push_pull_in  = i_handling_s_data ;
      end
    else
      begin
        open_drain_in = i_handling_s_data ;
        push_pull_in  = 1'b0 ;
      end
  end


//-- OD and PP modules instantiation ------------------------------------------

open_drain_behav_model u_open_drain_behav_model(

	  .i_behav_model  (open_drain_in)    ,
  	.o_behav_od    (open_drain_out)   ,
	  .sda            (sda)             );

push_pull_behav_model u_push_pull_behav_model(
	  .i_sda_push_pull   (push_pull_in)         ,
	  .i_push_pull_en    (push_pull_enable)     ,
	  .o_sda_push_pull   (push_pull_out)        ,
	  .sda               (sda)             );


endmodule

`default_nettype wire

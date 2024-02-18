`timescale 1us / 1ps

/*//////////////////////////////////////////////////////////////////////////////////
==================================================================================
 MIXEL GP 2024 LIBRARY
 Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
 CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2024 GP, INC.

 Authors: Omar Maghraby, Laila Tamer 
 
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

`default_nettype none
module ENTHDR_tb();

    // Clock and reset signals
    reg          i_clk_tb           ;
    reg          i_rst_n_tb         ;  
    reg          i_controller_en_tb     ;

   
    // Design Inputs           
    reg          i_i3c_i2c_sel_tb ;
    wire         sda_tb                 ;            
   
    // Design Output
    wire         o_sdr_rx_valid_tb     ;
    wire         o_ctrl_done_tb        ;
    wire         scl_tb                ; 
//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Nour Eldeen Samir 
// Revision:  
//
// Version : 1.0
// 
// Create Date:  5:28 PM     3/24/2023
// Design Name:  clk_divider 
// Module Name:  clk_divider 
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

module clk_divider (
	                input   wire    i_clk_in   ,  // XC7S15 FTGB196ABX FPGA Clk >> 100 MHZ (10 ns) 
	                input   wire    i_rst_n    ,
	                output  reg     o_clk_out );  // output divided clk by 2 >> 50 MHZ (20 ns)


always @(posedge i_clk_in or negedge i_rst_n)
  begin: clk_divider_by_2

    if(!i_rst_n)
      begin 
        o_clk_out <= 1'b0 ;
      end 

    else 
      begin 
        o_clk_out <= ~o_clk_out;  // delay of one clock cycle will be done by default so no need to count 
      end 

  end

endmodule 




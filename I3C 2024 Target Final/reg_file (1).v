//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Zyad Sobhy, Mostafa Hassan , Youssef Amr , Yaseen Salah
// Revision: Nour Eldeen Samir >>(editted 2nd always block)
//
// Version : 1.0
//
// Create Date:  7:46 PM     02/11/2022
// Design Name:  sdr_controller
// Module Name:  sdr_controller
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

module reg_file_c #(parameter WIDTH = 8 , DEPTH = 2**12 , ADDR = 12 )

	( input  wire			     i_regf_clk  		  ,   // clock , connected to the 50mhz clock , input from controller
	  input  wire			     i_regf_rst_n	     ,  	// active low reset , input from controller
	  input  wire			     i_regf_rd_en 	  ,  	// read data enable , input from controller
	  input  wire			     i_regf_wr_en 	  ,  	// write data enable, pulse at the end of the last bit , input from controller
	  input  wire [ADDR-1:0]  i_regf_addr  	  ,  	// adress of the reg file , input from controller
	  input  wire [WIDTH-1:0] i_regf_data_wr	  ,	// data write  , input from rx



/////////////////////////////////////////// HDR //////////////////////////////////////////
	  input wire  [ADDR-1:0]  i_engine_configuration      ,   // location of configuration it has only 2 values either normal conf = 1000 or dummy conf = 900

	  output reg [15:0]      o_frmcnt_data_len 			      ,
		output reg [2:0] 		   o_cccnt_CMD_ATTR 			      ,
		output reg [3:0]	     o_engine_TID 	 			        ,	 	
		output reg [7:0]		   o_ccc_CMD  	 	 	 	 	        ,
		output reg [4:0]	     o_cccnt_DEV_INDEX 	 	 	      ,
		output reg [2:0]		   o_frmcnt_DTT  	   	 	        ,
		output reg [2:0]		   o_engine_MODE  		 	 	      ,
		output reg  			     o_cccnt_RnW 	 		 		        ,
		output reg 				     o_cccnt_WROC 				        ,
		output reg 				     o_cccnt_TOC 		 	 	 	        ,
		output reg 				     o_engine_CP  		  	 	      ,
////////////////////////////////////////////////////////////////////////////////////////////


	  output reg              o_ser_rx_tx		  			   ,
	  output reg  [WIDTH-1:0] o_regf_data_rd    			   ,	// data read   ,  output to tx
	  output reg  [WIDTH-1:0] o_regf_num_frames 	 		   ,	
	  //outputs for crh
	  output reg  [WIDTH-1:0] o_crh_CRHDLY	 	 	  			,
	  output reg  [WIDTH-1:0] o_crh_getstatus_data 			,
	  output reg  [WIDTH-1:0] o_crh_CRCAP2	 	 	  			,
	  output reg  [WIDTH-1:0] o_crh_PRECR	 	 	  			,
	  output reg  [WIDTH-1:0] o_crh_cfg_reg	 	  			,
	  output reg  [WIDTH-1:0] o_crh_tgts_count     			,
	  output reg  [WIDTH-1:0] o_regf_ibi_cfg 	     			,
	  output reg  [WIDTH-1:0] o_regf_ibi_payload_size_reg ,
	  output reg  [WIDTH-1:0] o_i_ibi_tgt_address 			,
	  output wire [2:0]       o_regf_hj_cfg     				,
	  output wire             o_regf_hj_support 
	 );


//--------------------------------- parameters and defines in RegFile ------------------------------------------	
localparam ARBITRATION_REG_ADDRESS = 8'd48; 	
localparam IBI_CFG_REG_ADDRESS ='d101;	
localparam PAYLOAD_SIZE_REG_ADDRESS ='d102;
localparam EVENT_DISABLE_DIRECT_CCC_ADDRESS = 8'd103; // "Event" interrupt "DISEC" Direct location in RegFile 8'h81
localparam EVENT_DISABLE_BDCST_CCC_ADDRESS =8'd104; //Disable "Event" interrupt "DISEC" Broadcast location in RegFile 8'h01
localparam MDB_ADDRESS = 8'd107; //MDB location in RegFile
localparam BDCST_WRITE_ADDRESS = 8'd46; //  write for broadcasring location in RegFile 8'h7E
localparam EVENT_DISABLE_BYTE_ADDRESS=10'd392; //Disable Target Events Command Byte location in RegFile

//////////////////              CONTROLLER ROLE HANDOFF PARAMETERS              /////////////////
 localparam BROADCAST_ADDR_REG_FILE = 12'd46 ; //broadcast address in reg file (7E+w)
 localparam ARBITRATION_ADDR_REG_FILE = 9'd48 ; //arbitration address 
 localparam TARGET_ADDR_REG_FILE =  9'd0   ; 
 localparam GETSTATUS_ADDR_REG_FILE = 9'd387 ; 
 localparam GETMXDS_ADDR_REG_FILE = 9'd381    ; 
 localparam GETCAPS_ADDR_REG_FILE = 9'd384    ; 
 localparam DISEC_ADDR_REG_FILE = 9'd104    ; 
 localparam ENTAS0_ADDR_REG_FILE = 9'd393    ;
 localparam ENTAS1_ADDR_REG_FILE = 9'd394    ;
 localparam ENTAS2_ADDR_REG_FILE = 9'd395    ;
 localparam ENTAS3_ADDR_REG_FILE = 9'd396    ;
 localparam DEFTGTS_ADDR_REG_FILE = 9'd397   ;
 localparam GETACCCR_ADDR_REG_FILE  = 9'd389    ;
 localparam DEF_BYTE_REG_FILE = 9'd382    ;
 localparam CRCAPS1_ADDR_REG_FILE = 9'd385    ;
 localparam CRHDLY1_ADDR_REG_FILE = 9'd383    ; 
 localparam GETSTATUS_LSB_ADDR_REG_FILE = 9'd390    ;
 localparam CRCAPS2_ADDR_REG_FILE  = 9'd386    ;
 localparam PRECR_ADDR_REG_FILE = 9'd388 ; 
 localparam CRH_CFG_REG_FILE = 9'd407 ;
 localparam TGTS_COUNT_REG_FILE = 9'd35 ;
 localparam GETSTATUS_MSB_ADDR_REG_FILE = 9'd408 ;
 localparam DISEC_DATA_ADDR_REG_FILE  =  9'd406   ;



 localparam DUMMY_CONFIGURATION = 12'd450 ;
//--------------------------------- ----------------------------------- ------------------------------------------	
	


 reg [WIDTH-1:0] reg_array [DEPTH-1:0] ;  // 32 entry * 8 bits
 integer I, J ,K ;

/////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
reg [31:0] DWORD_0_Vector ;
reg [31:0] DWORD_1_Vector ;

always @(*) begin 
	DWORD_0_Vector [7:0]   = reg_array [i_engine_configuration] ;
	DWORD_0_Vector [15:8]  = reg_array [i_engine_configuration + 1] ;
	DWORD_0_Vector [23:16] = reg_array [i_engine_configuration + 2] ;  
	DWORD_0_Vector [31:24] = reg_array [i_engine_configuration + 3] ;  

	DWORD_1_Vector [7:0]   = reg_array [i_engine_configuration + 4] ;
	DWORD_1_Vector [15:8]  = reg_array [i_engine_configuration + 5] ;
	DWORD_1_Vector [23:16] = reg_array [i_engine_configuration + 6] ;  
	DWORD_1_Vector [31:24] = reg_array [i_engine_configuration + 7] ; 
end 

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////













  // Always checking on bit 0 of the frame, but we will only read it in ACK state when the data is Address 
  //assign o_ser_rx_tx  = reg_array[0][0] ; 

assign o_regf_hj_cfg      = reg_array[405][2:0] ;
assign o_regf_hj_support  = reg_array[409][0]   ;

 always @(posedge i_regf_clk or negedge i_regf_rst_n)
 	begin: regf_file_always
 		if (!i_regf_rst_n)
 			begin
 				
 				/////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
 				// DWORD0 for Dummy configuration .. that's a fixed configurations that doesn't change so it's made on the reset condition
 				// so whenever is needed to excute this dummy configuration the engine just has to give the input "i_engine_configuration" a value equals "DUMMY_CONFIGURATION" value .. say 'd 900
 				reg_array[DUMMY_CONFIGURATION]     <= 8'b1000_0001 ;		// 413
 				reg_array[DUMMY_CONFIGURATION + 1] <= 8'b1000_1111 ;		// 414
 				reg_array[DUMMY_CONFIGURATION + 2] <= 8'b0000_0000 ;		// 415
 				reg_array[DUMMY_CONFIGURATION + 3] <= 8'b0001_1000 ;		// 416 

				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////




 				o_regf_data_rd    <= 'b0 ;
 				o_regf_num_frames <= 'b0 ;     // editted by nour
				o_regf_ibi_cfg  <= 'b0 ;
 		   		o_regf_ibi_payload_size_reg <= 'b0 ;
 		   		o_i_ibi_tgt_address <= 'b0 ;

 				reg_array[TARGET_ADDR_REG_FILE]   <= 8'b10101000   	 ; // Target Address , Address[0] = 0 for TX, 1 for RX
 				reg_array[1]   <= 'b00000010    ; // Number of frames
 				reg_array[2]   <= 'b00000001  	 ;
 				reg_array[3]   <= 'b00000010  	 ;
 				reg_array[4]   <= 'b00000110  	 ;


 				for (I=5; I < 46 ; I = I +1) // SDR RX Data bytes
	 			reg_array[I] <= 'b0 ;

           for (J=50; J < 381 ; J = J +1) // UNUSED
                reg_array[J] <= 'b0 ;

 				reg_array[46]  <= 'b11111100 ; // 7'h7E broadcast address with rnw = 0 *write*
 				reg_array[47]  <= 'b11111101 ; // 7'h7E broadcast address with rnw = 1 *read*
 				reg_array[49]  <= 'b00000111 ; // ENTDAA CCC
 				reg_array[50]  <= 'b00100000 ; // 2024 : ENTHDR_DDR CCC (20 in hexadecimal)

 				//////////// Hot-Join Registers ////////////
 				reg_array[401] <= 'b00000000     ;   //ENEC CCC
 				reg_array[402] <= 'b00001011     ;   //ENEC BYTE //including ENINT, ENCR, ENHJ
 				reg_array[403] <= 'b00000001     ;   //DISEC CCC
 				reg_array[404] <= 'b00000000     ;   //DISEC BYTE //including DISINT, DISCR, DISHJ
 				//reg_array[405] <= 'bxxxxx000     ;   //HJ_CFG
 				reg_array[409] <= 'bxxxxx000  	 ;   //CRCAP1 
 				//reg_array[404] <= 'bxxxx0x00     ;   //DISEC BYTE //including DISINT, DISCR, DISHJ
 				reg_array[405] <= 'bxxxxx111     ;   //HJ_CFG
 				//reg_array[409] <= 'bxxxxx001  	 ;   //CRCAP1 

				//////////// IBI Registers ////////////
				reg_array[BDCST_WRITE_ADDRESS]<= 'b11111101 ; //'h7E/1 BDCST Write
 				reg_array[ARBITRATION_REG_ADDRESS]  <= 'b01010011 ; // Arbitration Address [7:1] = h9
 				reg_array[PAYLOAD_SIZE_REG_ADDRESS] <= 'b00000011 ; // PAYLOAD MAX SIZE
 				reg_array[EVENT_DISABLE_DIRECT_CCC_ADDRESS] <= 'h81       ; // "Event" interrupt "DISEC" Direct location in RegFile 8'h81
 				reg_array[EVENT_DISABLE_BDCST_CCC_ADDRESS] <= 'h01; //Disable "Event" interrupt "DISEC" Broadcast location in RegFile 8'h01
 				reg_array[EVENT_DISABLE_BYTE_ADDRESS] <= 'b00001011 ; // Disable Target Events Command Byte location in RegFile 8'b00001011
 				reg_array[IBI_CFG_REG_ADDRESS] <= 'b00000001 ; /// Ack + mdb only 

              //// controller role registers //////
               reg_array[BROADCAST_ADDR_REG_FILE]   <= {7'h7E , 1'b0} ; //broadcast address 7'h7E + W = 8'hFC  
               reg_array[GETSTATUS_ADDR_REG_FILE]   <= 'h90 ;
               reg_array[GETMXDS_ADDR_REG_FILE]   <= 'h94 ;
               reg_array[GETCAPS_ADDR_REG_FILE]   <= 'h95 ; 
               reg_array[DISEC_ADDR_REG_FILE]   <= 'h01 ;
               reg_array[ENTAS0_ADDR_REG_FILE]   <= 'h02 ;
               reg_array[ENTAS1_ADDR_REG_FILE]   <= 'h03 ;
               reg_array[ENTAS2_ADDR_REG_FILE]   <= 'h04 ;
               reg_array[ENTAS3_ADDR_REG_FILE]   <= 'h05 ;
               reg_array[DEFTGTS_ADDR_REG_FILE]   <= 'h08 ;
               reg_array[GETACCCR_ADDR_REG_FILE]   <= 'h91 ;
               reg_array[DEF_BYTE_REG_FILE]        <= 'h91 ; 
               reg_array[DISEC_DATA_ADDR_REG_FILE] <= 'h09 ; //hot join disabled + interrupts disabled
               //for testing 
               reg_array[ARBITRATION_ADDR_REG_FILE]  <= 'b01010011 ;
               reg_array[CRHDLY1_ADDR_REG_FILE] <= 'h02 ;
               reg_array[GETSTATUS_LSB_ADDR_REG_FILE] <= 'h02 ;
               reg_array[CRCAPS2_ADDR_REG_FILE] <= 'h02 ;
               reg_array[PRECR_ADDR_REG_FILE] <= 'h02 ;
               reg_array[CRH_CFG_REG_FILE] <= 'h01 ;
               reg_array[TGTS_COUNT_REG_FILE] <= 'h02 ;

                for (K=454; K< DEPTH; K = K +1) 	 	
                reg_array[K] <= 'b0 ;
               
               
               o_crh_CRHDLY <= reg_array[CRHDLY1_ADDR_REG_FILE] ;
               o_crh_getstatus_data <= reg_array[GETSTATUS_LSB_ADDR_REG_FILE] ;
               o_crh_CRCAP2 <= reg_array[CRCAPS2_ADDR_REG_FILE] ;
               o_crh_PRECR <= reg_array[PRECR_ADDR_REG_FILE] ;
               o_crh_cfg_reg <= reg_array[CRH_CFG_REG_FILE] ;
               o_crh_tgts_count <= reg_array[TGTS_COUNT_REG_FILE] ; 

 			end
 		else
 		  begin


 		  	/////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
 		  		o_frmcnt_data_len <= DWORD_1_Vector [31:16] ;

 		  		o_cccnt_CMD_ATTR  <= DWORD_0_Vector [2:0]   ;
 		  		o_engine_TID 	 	<= DWORD_0_Vector [6:3]   ;
 		  		o_ccc_CMD  	 	 	<= DWORD_0_Vector [14:7]  ;
 		  		o_engine_CP  		<= DWORD_0_Vector [15]    ;
 		  		o_cccnt_DEV_INDEX <= DWORD_0_Vector [20:16] ;
 		  		o_frmcnt_DTT  	   <= DWORD_0_Vector [25:23] ;
 		  		o_engine_MODE  	<= DWORD_0_Vector [28:26] ;
 		  		o_cccnt_RnW 	 	<= DWORD_0_Vector [29]    ;
 		  		o_cccnt_WROC 		<= DWORD_0_Vector [30]    ;
 		  		o_cccnt_TOC 		<= DWORD_0_Vector [31]    ;


 		  		reg_array [i_engine_configuration - 1] = 8'b0000_0000 ; //zerozzzz location to ba serialized in ZEROS state 

			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////







 		    o_crh_CRHDLY <= reg_array[CRHDLY1_ADDR_REG_FILE] ;
                                 o_crh_getstatus_data <= reg_array[GETSTATUS_LSB_ADDR_REG_FILE] ;
                                 o_crh_CRCAP2 <= reg_array[CRCAPS2_ADDR_REG_FILE] ;
                                 o_crh_PRECR <= reg_array[PRECR_ADDR_REG_FILE] ;
                                 o_crh_cfg_reg <= reg_array[CRH_CFG_REG_FILE] ;
                                 o_crh_tgts_count <= reg_array[TGTS_COUNT_REG_FILE] ; 
                                 
                                                          
 		    o_regf_num_frames <= reg_array[1]     ; //editted by nour
		    o_ser_rx_tx       <= reg_array [0][0] ; //Yaseen's Edit

		   o_regf_ibi_cfg  <= reg_array[IBI_CFG_REG_ADDRESS];
 		   o_regf_ibi_payload_size_reg <= reg_array[PAYLOAD_SIZE_REG_ADDRESS];
 		   o_i_ibi_tgt_address <= reg_array[ARBITRATION_REG_ADDRESS]; //Arbitrated Address
			
 		    if (i_regf_rd_en && !i_regf_wr_en)  // read // enable should be a pulse
 			  begin
 				o_regf_data_rd <= reg_array [i_regf_addr] ;
 			  end
 		    else if (i_regf_wr_en && !i_regf_rd_en)  // write
 			  begin
 			  	reg_array [i_regf_addr] <= i_regf_data_wr ;
 			  end

 			//////////// ENHJ/DISHJ Defining-Bits Logic ////////////
 			if (reg_array[409][0] && reg_array[405][1]) //CRCAP1[0] supports hot-join & HJ_CFG[2] enables hot-join
 				begin
 					reg_array[402][3] <= 1'b1 ; //ENEC_BYTE[3]  >> ENHJ=1
 					reg_array[404][3] <= 1'b0 ; //DISEC_BYTE[3] >> DISHJ=0
 				end
 			else
 				begin
 					reg_array[402][3] <= 1'b0 ; //ENEC_BYTE[3]  >> ENHJ=0
 					reg_array[404][3] <= 1'b1 ; //DISEC_BYTE[3] >> DISHJ=1
 				end
 		  end

 	end


endmodule
`default_nettype wire


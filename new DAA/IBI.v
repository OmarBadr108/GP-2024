`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Mixel inc.
// Engineer: Zyad Sobhy
// 
// Create Date: 03/11/2023 05:16:24 PM
// Design Name: 
// Module Name: IBI
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module IBI(
    input        i_ibi_clk,
    input        i_ibi_rst_n,
    input        i_ibi_en,
    input        i_ibi_scl_neg_edge,
    input        i_ibi_scl_pos_edge,
    input  [7:0] i_ibi_bcr_reg,
    input  [7:0] i_ibi_cfg_reg,
    input  [7:0] i_ibi_payload_size_reg,
    input  [7:0] i_ibi_tgt_address,
    input        i_ibi_ser_mode_done,
    input        i_ibi_scl,
    input        i_ibi_rx_mode_done,
    input        i_ibi_payload_done,
    input        i_ibi_ack_nack,
   
    output reg       o_ibi_pp_od,    
    output reg [9:0] o_ibi_regf_address,
    output reg       o_ibi_regf_rd_en,
    output reg       o_ibi_rx_en,
    output reg       o_ibi_tx_en,
    output reg       o_ibi_regf_wr_en,
    output reg [2:0] o_ibi_rx_mode,
    output reg [2:0] o_ibi_tx_mode,
    output reg       o_ibi_payload_en,
    output reg       o_ibi_cnt_en,
    output reg       o_ibi_ser_rx_tx ,
    output reg       o_ibi_done
   );
   
   
//-------------------------------- states encoding in Binare ----------------------------------------------

localparam IDLE     	             = 5'b00000 ; 
localparam ACK       	             = 5'b00001 ;
localparam NACK       	             = 5'b00010 ;
localparam MDB       	             = 5'b00011 ;
localparam PAYLOAD    		         = 5'b00100 ;
localparam REP_START                 = 5'b00101 ;
localparam BDCST                     = 5'b00110 ;
localparam DISABLE_ALL_INT           = 5'b00111 ;
localparam DISABLE_TGT_INT           = 5'b01000 ;
localparam DISABLE_INT_CCC_BDCST     = 5'b01001 ;
localparam DISABLE_INT_CCC_DIRECT    = 5'b01010 ;
localparam DISABLE_INT_BYTE          = 5'b01011 ;
localparam END_IBI                   = 5'b01100 ;
localparam TGT_ADDRESS               = 5'b01101 ;
localparam MDB_T_BIT                 = 5'b01110 ;
localparam STOP                      = 5'b01111 ;
localparam PARITY                    = 5'b10000 ;
localparam TGT_ACK                   = 5'b10001 ;



//--------------------------------- parameters and defines ------------------------------------------
/*To get BCR from Target Address :
 1) Target Address value - 7'h08 = Target index
 2) Base Address + 6 + 8*(Target index)
h08 -> 206
h09->  214
h10->  222
H11 -> 230
*/
localparam FIRST_TGT_ADDRESS = 7'h08;
localparam BASE_ADDRESS = 200; 
localparam OFFSET = 6;
localparam TGT_ADDR_OFFSET = 8;

//--------------------------------- parameters and defines in RegFile ------------------------------------------
localparam MDB_ADDRESS = 8'd107; //MDB location in RegFile
localparam BDCST_WRITE_ADDRESS = 8'd46; //  write for broadcasring location in RegFile 8'h7E
localparam EVENT_DISABLE_DIRECT_CCC_ADDRESS = 8'd103; // "Event" interrupt "DISEC" Direct location in RegFile 8'h81
localparam EVENT_DISABLE_BDCST_CCC_ADDRESS =8'd104; //Disable "Event" interrupt "DISEC" Broadcast location in RegFile 8'h01
localparam EVENT_DISABLE_BYTE_ADDRESS=10'd392; //Disable Target Events Command Byte location in RegFile 8'b00001011
localparam ARBITRATION_REG_ADDRESS = 8'd48; 
localparam PAYLOAD_SIZE_REG_ADDRESS ='d102;	
localparam IBI_CFG_REG_ADDRESS ='d101;



//--------------------------------- internal wires declaration ------------------------------------------
reg [4:0] state ;
reg [1:0] end_ibi_flag;
reg [1:0] parity_to_SR_flag;
reg tgt_address_flag;
//--------------------------------- shift rx mode done 2 cycles ------------------------------------------

reg i_ibi_rx_mode_done_ff1, i_ibi_rx_mode_done_ff2;
always @(posedge i_ibi_clk or negedge i_ibi_rst_n )
    begin
      i_ibi_rx_mode_done_ff1 <= i_ibi_rx_mode_done; 
      i_ibi_rx_mode_done_ff2 <= i_ibi_rx_mode_done_ff1;
    end
//----------------------------------Pulse Generator for RegFile wr_en ------------------------------------//
reg ibi_regf_wr_en;
reg regf_wr_en_prev;
  
always@(posedge i_ibi_clk or negedge i_ibi_rst_n )
    begin
    if (!i_ibi_rst_n) 
      regf_wr_en_prev  <= 1'b0;
    else    
      regf_wr_en_prev  <=   ibi_regf_wr_en ;  
      o_ibi_regf_wr_en <= ~(regf_wr_en_prev) & ibi_regf_wr_en ;
    end
//----------------------------------Pulse Generator for tx mode done ------------------------------------//
reg ibi_ser_mode_done_prev;
reg ibi_ser_mode_done_pulse;

  
always@(posedge i_ibi_clk or negedge i_ibi_rst_n )
    begin
    if (!i_ibi_rst_n) 
      regf_wr_en_prev  <= 1'b0;
    else    
      ibi_ser_mode_done_prev  <=   i_ibi_ser_mode_done ;  
      ibi_ser_mode_done_pulse <= ~(ibi_ser_mode_done_prev) & i_ibi_ser_mode_done ;
    end
//--------------------------------- shift ser mode done 3 cycles ------------------------------------------

reg i_ibi_tx_mode_done_ff1, i_ibi_tx_mode_done_ff2, i_ibi_tx_mode_done_ff3;
always @(posedge i_ibi_clk or negedge i_ibi_rst_n )
    begin
      i_ibi_tx_mode_done_ff1 <= i_ibi_ser_mode_done; 
      i_ibi_tx_mode_done_ff2 <= i_ibi_tx_mode_done_ff1;
      i_ibi_tx_mode_done_ff3 <= i_ibi_tx_mode_done_ff2;
    end

//--------------------------------- controller main fsm ---------------------------------------------------

always @(posedge i_ibi_clk or negedge i_ibi_rst_n) 
  begin: IBI
    
    if (!i_ibi_rst_n) 
    	begin
    	state <= IDLE;
    	o_ibi_pp_od <= 1'b0;
    	o_ibi_regf_address <= 8'b0;
        o_ibi_regf_rd_en   <= 1'b0;
        ibi_regf_wr_en     <= 1'b0;
        o_ibi_rx_mode      <= 3'b0;
        o_ibi_tx_mode      <= 3'b0;
        o_ibi_done         <= 1'b0;
        o_ibi_tx_en        <= 1'b0;
        o_ibi_rx_en        <= 1'b0;
        o_ibi_payload_en   <= 1'b0;
        o_ibi_ser_rx_tx    <=1'b0;
        end_ibi_flag       <= 2'b00;
        o_ibi_cnt_en       <= 1'b0;
    	end

    else
    	begin
    		case(state)
    		IDLE: begin
                  if (i_ibi_en) // Received in SCL High    		
                     begin
                        if (i_ibi_cfg_reg[0]) // CTRLR ACK/NACK
                            begin
                                o_ibi_regf_rd_en <=1'b1; 
                                o_ibi_regf_address <= ((i_ibi_tgt_address[7:1] - FIRST_TGT_ADDRESS) << 3) + OFFSET + BASE_ADDRESS ; // to get the target BCR register Address
                                    if (i_ibi_scl_neg_edge)
                                        begin
                                        state <= ACK;
                                        o_ibi_tx_en <= 1'b1;
                                        o_ibi_tx_mode <= 3'b100;//CTRL ACK OPen-Drain 0
                                        o_ibi_pp_od <= 1'b0;
                                        end
                            end
                        else 
                            begin
                                if (i_ibi_scl_neg_edge)
                                   begin
                                   state <= NACK;
                                   o_ibi_tx_en <= 1'b0; 
                                   o_ibi_pp_od <= 1'b0;
                                   end
                            end
                     end
                 else   
                      begin  
                         o_ibi_tx_en        <= 1'b0;
                      end
    		      end
    		      
    		ACK: begin  //Entered in LOW SCL with TX driving 0 OD
                  if(i_ibi_scl)  	//wait for HIGH SCL level
                    begin 		 
                    if (i_ibi_bcr_reg[2])
                     //0 : No data after IBI.. 1: MDB then Payload the payload continuity determined by T-bit  
                        begin
                           state <= MDB ; 
                           o_ibi_regf_rd_en <=1'b0;
                           o_ibi_cnt_en <= 1'b1;
                           o_ibi_rx_en <= 1'b1;
                           o_ibi_tx_en <= 1'b0;
                           o_ibi_pp_od <= 1'b1;
                           o_ibi_rx_mode <= 3'b001; //Deserializing
                        end
                    else 
                        begin  		                      
    		              state <= STOP;
                        end
                    end   
    	         end
    	         
    	         
    	         
    	         
    	    MDB: begin
    	         if(i_ibi_rx_mode_done_ff1)          
    	           begin
    	            ibi_regf_wr_en <= 1'b1;
    	           end
    	          if(i_ibi_rx_mode_done_ff2)     
    	            begin   
    	               o_ibi_regf_address <= MDB_ADDRESS; //MDB location in RegFile
    	                    if (!i_ibi_scl)
    		                  begin
    	                       o_ibi_rx_en <= 1'b0;
    	                       o_ibi_cnt_en <= 1'b0;
    	                       state <= MDB_T_BIT;
    	                       o_ibi_tx_mode <= 3'b100; // driving SDA LOW to create SR 
    	                      end
    	            end       	              
    	         end     
    	         
    	         
    	    MDB_T_BIT:begin     
    	                    ibi_regf_wr_en <= 1'b0;
    	                   if (!i_ibi_cfg_reg[1]) // Additional Payload: 1: Read .. 0:Terminate
    	                       begin  
    	                           if (i_ibi_scl)
    		                         begin
    		                          o_ibi_tx_mode <= 3'b100; // driving SDA LOW to create SR
    		                          state <= STOP;
    		                          o_ibi_tx_en <= 1'b1;
    		                         end
    		                   end      
    	                   else     
    	                        begin
    	                            state <= PAYLOAD;
    	                            o_ibi_payload_en <= 1'b1;  
                                    o_ibi_ser_rx_tx <=1'b1;
    	                        end
    	              end         
    	         
    	         
    	         
    	         
    	    PAYLOAD: begin      
    	               // same process as Data-In Sdr mode 
    	               // 8-bit frame then a T-bit with specific number of frames to be received 
    	               // SDR take payload enable signal 
    	               // frame counter take payload max no frames RegFile[102]   
                        if (i_ibi_payload_done)	    
                            begin
                            o_ibi_payload_en <= 1'b0;
                             o_ibi_done  <= 1'b1;
                             o_ibi_ser_rx_tx <= 1'b0;
    		                state <= IDLE;
                            end       
    	             end  
    		     
 // SDA should be maintained high during both low&high of SCL during ack bit    		     
 // then high for the next low of SCL and then go down in High SCL making Rep. Start
 
    		NACK: begin // Entered in LOW SCL with TX driving High imp. OD
    		    if(i_ibi_scl) //wait for HIGH
    		      begin
    		        if (i_ibi_cfg_reg[3:2] == 2'b00) // Keep IBI enabled 
                      begin                      
                       state <= STOP;
                      end    
                    else     
                      begin   
                        state <= REP_START;
                        end_ibi_flag <= 2'b00;
                        o_ibi_tx_mode <= 3'b100; // driving SDA LOW PP
                        o_ibi_tx_en <= 1'b1;
                     end
                  end   
    		     end
    		      
    		      
    		REP_START: begin  
                             o_ibi_pp_od <= 1'b1;
                             if (end_ibi_flag == 2'b01) 
                                begin
                                    o_ibi_tx_mode <= 3'b100; // driving SDA LOW PP
                                    o_ibi_done <= 1'b1;
                                    state <= IDLE;
                                end
                             else if (end_ibi_flag == 2'b00) // Entered in HIGH SCL with TX driving High imp. OD 
                                begin
                                    state <= BDCST; 
                                    o_ibi_tx_mode <= 3'b001; // Serializing
                                    o_ibi_regf_rd_en   <= 1'b1 ; 
                                    o_ibi_regf_address <= BDCST_WRITE_ADDRESS; // 8'h7E/write for broadcasring
                                    o_ibi_cnt_en <= 1'b1;
                                end    
                                
                             else if (end_ibi_flag == 2'b10)
                                begin
                                  o_ibi_tx_mode <= 3'b000; // Rep_Start
                                  if (i_ibi_ser_mode_done)
                                     begin   
                                        o_ibi_regf_address <= ARBITRATION_REG_ADDRESS;//((i_ibi_tgt_address[7:1] - FIRST_TGT_ADDRESS) * 4'd9) + TGT_ADDR_OFFSET + BASE_ADDRESS;
                                     end   
                                  if(ibi_ser_mode_done_pulse)
                                     begin 
                                        state <= TGT_ADDRESS; 
                                        o_ibi_tx_en <= 1'b1;
                                        o_ibi_tx_mode  <= 3'b001;
                                        o_ibi_cnt_en <= 1'b1; 
                                     end   
                                end        
    		           end
    		           
    		BDCST: begin // Entered in HIGH SCL with TX driving 0 PP TX enabled
                         if (i_ibi_tx_mode_done_ff2)   // Entered in the low SCL of last bit 
                            begin      
                               state <= TGT_ACK;
                               o_ibi_pp_od <= 1'b0;
                               o_ibi_tx_en <= 1'b0;
                               o_ibi_rx_en <= 1'b1;
                               o_ibi_rx_mode <= 3'b0; //ACK mode
                               o_ibi_regf_rd_en <= 1'b1; 
                               o_ibi_cnt_en <= 1'b0;
                            end       
    		       end
    		       
    		DISABLE_INT_CCC_BDCST: begin       
    		                  if (!i_ibi_scl)
    		                      begin
    		                          o_ibi_tx_en  <= 1'b1;
    		                          o_ibi_pp_od  <= 1'b1;
    		                          o_ibi_tx_mode <= 3'b001; //Serializing mode
    		                      end
    		                  if (i_ibi_tx_mode_done_ff1)
    		                      begin
    		                          o_ibi_cnt_en <= 1'b0; 
    		                          o_ibi_tx_mode <= 3'b011; //Parity mode
                                      o_ibi_regf_address <= EVENT_DISABLE_BYTE_ADDRESS; //Disable Target Events Command Byte
                                      state <= PARITY;
                                      parity_to_SR_flag <= 2'b00;
                                  end    
                             end     
                             
            PARITY: begin
                       if(parity_to_SR_flag == 2'b11)
    		                       begin
    		                         if (ibi_ser_mode_done_pulse)
    		                              begin
    		                                  o_ibi_regf_rd_en <= 1'b1;
    		                                  o_ibi_cnt_en <= 1'b0; 
    		                                  end_ibi_flag <= 2'b10;
                                              state <= REP_START;
                                          end    
                                   end       
                	   else 
                	       begin
                	           if (ibi_ser_mode_done_pulse)                	   
    		                      begin
    		                          if(parity_to_SR_flag == 2'b00)
    		                              begin
    		                                  o_ibi_regf_rd_en <= 1'b1;
    		                                  o_ibi_cnt_en <= 1'b1; 
    		                                  o_ibi_tx_mode <= 3'b001; //Serializing mode
                                              state <= DISABLE_INT_BYTE;
                                          end    
                                      if(parity_to_SR_flag == 2'b01)
    		                              begin
    		                                  o_ibi_regf_rd_en <= 1'b1;
    		                                  o_ibi_cnt_en <= 1'b0; 
    		                                  o_ibi_tx_mode <= 3'b010; //STOP mode
                                              state <= STOP;
                                          end                              
                                  end         
                            end    
                    end              
                    
            TGT_ACK: begin       
                   if(i_ibi_scl) 
                    begin
                     if (i_ibi_ack_nack)
                        begin
                            o_ibi_cnt_en <= 1'b1;
                            o_ibi_rx_en  <= 1'b0;
                            o_ibi_tx_mode <= 3'b100; // Driving 0 once it enabled to create Ack handoff
                            if (tgt_address_flag)
                                begin
                                    state <= DISABLE_INT_BYTE;
                                    o_ibi_regf_rd_en <= 1'b1;
    		                        o_ibi_cnt_en <= 1'b1; 
                                    o_ibi_regf_address <= EVENT_DISABLE_BYTE_ADDRESS; // "Event" interrupt "DISEC" Direct
                                end
                           else     
                             begin
                                if (i_ibi_cfg_reg[3:2] == 2'b01) //disable Direct tgt 
                                   begin
                                      state <= DISABLE_INT_CCC_DIRECT;
                                      o_ibi_regf_address <= EVENT_DISABLE_DIRECT_CCC_ADDRESS; // "Event" interrupt "DISEC" Direct
                                   end   
                                else if (i_ibi_cfg_reg[3:2] == 2'b11)// disable for all tgts           
                                    begin
                                      state <= DISABLE_INT_CCC_BDCST;
                                      o_ibi_regf_address <= EVENT_DISABLE_BDCST_CCC_ADDRESS; //Disable "Event" interrupt "DISEC" Broadcast
                                    end    		                
                             end        
                        end
                     else    
                        begin
                          state <= STOP;
                        end
                    end
                  end      
                    
          DISABLE_INT_CCC_DIRECT: begin       
                             if (!i_ibi_scl)
    		                      begin
    		                          o_ibi_tx_en  <= 1'b1;
    		                          o_ibi_pp_od  <= 1'b1;
    		                          o_ibi_tx_mode <= 3'b001; //Serializing mode
    		                      end  
    		                  if (i_ibi_tx_mode_done_ff1)
    		                      begin
    		                            o_ibi_tx_mode <= 3'b011; //Parity mode
    		                            o_ibi_cnt_en <= 1'b0;  
                                        state <= PARITY;
                                        parity_to_SR_flag <= 2'b11;
                                  end    
                             end    
    		                  
    		TGT_ADDRESS : begin
    		                o_ibi_tx_mode <= 3'b001;  
    		                if (ibi_ser_mode_done_pulse) 
    		                  begin
    		                    o_ibi_pp_od <= 1'b0;
    		                    o_ibi_tx_en <= 1'b0;
    		                  end
    		                if(!i_ibi_scl && i_ibi_tx_mode_done_ff3)
    		                      begin
    		                          o_ibi_regf_rd_en   <= 1'b1  ; 
    		                          o_ibi_cnt_en <= 1'b0;
                                      o_ibi_regf_address <= EVENT_DISABLE_BYTE_ADDRESS; //Disable Target Events Command Byte
                                      state <= TGT_ACK;
                                      tgt_address_flag <=1'b1;
                                      o_ibi_rx_en <= 1'b1;
                                      o_ibi_rx_mode <= 3'b0; //ACK mode
                                  end       
                          end        
    		              
    		              
    		DISABLE_INT_BYTE: begin 
    		                   o_ibi_regf_rd_en <= 1'b1;
    		                   o_ibi_tx_en <= 1'b1;
    		                  if (!i_ibi_scl)
    		                      begin
    		                          o_ibi_tx_en  <= 1'b1;
    		                          o_ibi_pp_od  <= 1'b1;
    		                          o_ibi_tx_mode <= 3'b001; //Serializing mode
    		                      end
    		                  if (ibi_ser_mode_done_pulse)
    		                      begin
    		                          o_ibi_cnt_en <= 1'b0; 
    		                          o_ibi_tx_mode <= 3'b011; //Parity mode
                                      o_ibi_regf_address <= EVENT_DISABLE_BYTE_ADDRESS; //Disable Target Events Command Byte
                                      state <= PARITY;
                                      parity_to_SR_flag <= 2'b01;
                                  end                   
    		                  end
    		                 
    		                 
    		END_IBI:         begin       // Entered from NACK in High SCL with TX driving High Imp 
                              o_ibi_pp_od <= 1'b1; // Rep. Start is PP      		
                             // o_ibi_tx_mode <= 3'b101; // Driving 1... in case of ACK this creating a STOP
                              ibi_regf_wr_en <= 1'b0;
    		                  if (!i_ibi_scl) // wait for Low SCL and maintaing High imp.
    		                      begin
    		                          end_ibi_flag <= 2'b01;
    		                          o_ibi_tx_mode <= 3'b100; // Driving 0
    		                          state <= REP_START;
    		                      end    
    		                 end     
    		                 
    		                     
    		 STOP :    begin      
    		             ibi_regf_wr_en <= 1'b0; 
    		             if (!i_ibi_scl)
    		                  begin
    		                      o_ibi_tx_en <= 1'b1;
    		                      o_ibi_tx_mode <= 3'b010; //STOP
    		                  end
                       else  if (i_ibi_ser_mode_done)
                            begin 
                                 state       <= IDLE ;
                                 o_ibi_done  <= 1'b1;
                                 o_ibi_tx_en <= 1'b0;
                             end 
                       end      
    		       
    		
    		endcase
    	end

  end

   
endmodule

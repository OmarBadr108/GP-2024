module ddr_mode (
input        i_sys_clk,
input        i_sys_rst,
input        i_engine_en,
input        i_frmcnt_last,
input        i_bitcnt_done,
input        i_tx_mode_done,
input        i_rx_mode_done,
input        i_rx_second_pre,
input        i_sclgen_pos_edge,
input        i_sclgen_neg_edge,
input        i_sclstall_stall_done,  // NO NEED TILL NOW
input        i_regf_wr_rd_bit,
input        i_rx_error,


output reg       o_sclstall_en,         // NO NEED TILL NOW
output reg       o_sclstall_no_of_cycles, // NO NEED TILL NOW
output reg       o_tx_en,
output reg [3:0] o_tx_mode,
output reg       o_rx_en,
output reg [3:0] o_rx_mode,
output reg       o_bitcnt_en,
output reg       o_frmcnt_en,
output reg       o_bitcnt_err_rst,
output reg       o_sdahand_pp_od,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [4:0] o_regf_addr,
output reg       o_engine_done
);

// tx modes needed  
localparam [2:0]  tx_idle = 'b000,
                  Reserved_preamble = 'b000,
                  special_preamble_tx = 'b001,
                  one_preamble = 'b010,
                  zero_preamble = 'b1000,
                  Serializing_First_byte = 'b101,
                  Serializing_Second_byte = 'b100,
                  Calculating_Parity ='b0101,
                  token_CRC = 'b110,
                  stall = 'b111;
				  
				  
 // rx modes neede 
localparam [2:0]     rx_idle = 'b000,
                     preamble = 'b000,
                     special_preamble_rx = 'b001, //for recieving 01
                     Deserializing_First_byte = 'b010,
                     Deserializing_Second_byte = 'b011, 
                     Check_token = 'b100,
                     Check_Parity_value = 'b101,
                     CRC_received = 'b110,
                     Error = 'b111;

// fsm states
localparam [3:0]    idle = 'b0000,
                    first_stage_command_Pre = 'b0001,
                    command_word = 'b0010,
					          address = 'b0011,               // broadcast or dierecet 
					          parity = 'b0101,
					          sec_stage_first_data_pre = 'b0110,             // sent by controller
					          ack_waiting = 'b0111,
					          first_data_byte = 'b0100,
					          second_data_byte = 'b1000,
					          dummy_data_byte = 'b1001,            // in case of sending or recieving only 8 bits
					          third_stage_first_data_pre = 'b1010,             // send by target or controller
					          abort_bit = 'b1011,                      //   aborting by controller or target             
					          fourth_stage_crc_pre = 'b1100,
					          token_crc_bits = 'b1101,                 // 4 bits
					          crc_value_bits = 'b1110,                  // 5 bits 
					          error = 'b1111;
					
					

                     
reg    [1:0]         current_state,
                     next_state ;
					 
					 
					 
always @(posedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
     current_state <= idle ;
   end
  else
   begin
     current_state <= next_state ;
   end
 end


always @(*)
 begin
   
  o_sdahand_pp_od = 'b1 ;  // default pp 
  o_tx_en = 'b0 ; 
  o_rx_en = 'b0 ;
	o_rx_mode = rx_idle ;
  o_bitcnt_en = 'b1 ;
  o_frmcnt_en = 'b1 ;
  o_regf_wr_en = 'b0 ;
  o_regf_rd_en = 'b0 ;
  o_engine_done = 'b0 ;
  o_bitcnt_err_rst = 'b0 ;
	o_regf_addr = 'b0; //ay 7aga talama m4 h3ml serializing mn regf
  
  
  case(current_state)
  
  idle : begin 
          
		  o_bitcnt_en = 'b0;
		  o_frmcnt_en = 'b0 ;
		  o_tx_mode = tx_idle ; 

		  end
		  
		 		  		  
  first_stage_command_Pre :  begin
           
		   o_tx_en = 'b1 ;
		   o_tx_mode = first_stage_command_Pre ;
   
		   end 
           		   
	
  command_word	: begin 
    
		  o_tx_en = 'b1;
		  o_tx_mode = Serializing_First_byte ; //????? ??? ??? ??? ????? ??????? ??? ????? ???? ?????? ?????
		  o_regf_addr = ;// undetermined yet0 
		  o_regf_rd_en = 'b1 ;
		  
            end 
            
  
  address : begin 
    
      o_tx_en = 'b1;
		  o_tx_mode = Serializing_Second_byte ;
		  o_regf_addr = // undetermined yet0 
		  o_regf_rd_en = 'b1 ;
		  
		  end
    
  
  parity        : begin
    
      o_tx_en = 'b1;
		  o_tx_mode = Calculating_Parity ;

             end 
			 
  
 sec_stage_first_data_pre : begin 
   
      o_tx_en = 'b1;
      o_tx_mode = one_preamble ;
  
             end 
			 
  
  ack_waiting        : begin
    
      o_rx_en = 'b1 ;
	    o_rx_mode = preamble ;

             end 


  first_data_byte        : begin
    
    if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_First_byte;
  		   o_regf_addr = // undetermined yet0 
		   o_regf_rd_en = 'b1 ;
      end
       
     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_First_byte ;
	     o_regf_addr = // undetermined yet0 
		   o_regf_wr_en = 'b1 ;
	    end 

             end
             
             
  second_data_byte        : begin
    
    if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_First_byte;
  		   o_regf_addr = // undetermined yet0 
		   o_regf_rd_en = 'b1 ;
      end
       
     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_First_byte ;
	     o_regf_addr = // undetermined yet0 
		   o_regf_wt_en = 'b1 ;
	    end  
			 
  
  dummy_data_byte   : begin



             end 
			 

  third_stage_first_data_pre    : begin
    
        if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
          o_tx_mode = one_preamble;
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;
         end
 
             end 
			 

  abort_bit      : begin
    
       if (i_regf_wr_rd_bit)
         begin
          if (!i_frmcnt_last)
            begin
              o_tx_en = 'b1;
              o_tx_mode = one_preamble;
            end
          else
            begin
              o_tx_en = 'b1;
              o_tx_mode = zero_preamble;
            end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;
         end



             end 


  fourth_stage_crc_pre     : begin
    
    if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
          o_tx_mode = special_preamble;
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = special_preamble;
         end

             end 
             
   
   token_crc_bits        : begin



             end 			 

	
   crc_value_bits   : begin



             end 
			 
   
   error   : begin
     
          o_rx_en = 'b1;
          o_rx_mode = Error;

             end
      endcase
    end
    
    
    always @ (*)
    
     begin
       
       case(current_state)
         
         idle : begin 
           
           if (i_engine_en) 
		         next_state = first_stage_command_Pre ;
		       else
		         next_state = idle ;
		       
		         end
		         
		         
		      first_stage_command_Pre :  begin
		      		        
		        if (i_tx_mode_done)
		          next_state = command_word ;
		        else
		          next_state = first_stage_command_Pre ;
		          
		          end
		          
		           
		      command_word	: begin 
		        
		        if (i_tx_mode_done)
		          next_state = address ;
		        else
		          next_state = command_word ;
		          
		          end
		          
		          
		      address	: begin 
		        
		        if (i_tx_mode_done)
		          next_state = parity ;
		        else
		          next_state = address ;
		          
            end 
            
            
		      parity	: begin 
		        
		        if (i_tx_mode_done)
		          next_state = parity ;
		        else
		          next_state = sec_stage_first_data_pre ;
		          
            end
            
            
 		      sec_stage_first_data_pre	: begin 
		        
		        if (i_tx_mode_done)
		          next_state = sec_stage_first_data_pre ;
		        else
		          next_state = ack_waiting ;
		          
            end
            
          
  		       ack_waiting	: begin 
		        
		        if (i_rx_mode_done)
		          next_state = first_data_byte ;
		        else
		          next_state = ack_waiting ;
		          
            end 
            
            
  		       first_data_byte	: begin 
		        
		        if (i_rx_mode_done)
		          next_state = second_data_byte ;
		        else
		          next_state = first_data_byte ;
		          
            end
            
           second_data_byte	: begin 
		        
		        if (i_rx_mode_done)
		          next_state = second_data_byte ;
		        else
		          next_state = second_data_byte ;
		          
            end  
       
       
     endcase
   end
       
       

             
endmodule

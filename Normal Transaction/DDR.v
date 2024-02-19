module ddr_mode (
input        i_sys_clk,
input        i_sys_rst,
input        i_engine_en,
input        i_frmcnt_last,
input        i_tx_mode_done,
input        i_rx_mode_done,
input        i_rx_pre,
input        i_regf_wr_rd_bit,
input        i_rx_error,
input        i_engine_ter,    // انبوت يحدد انا هترمنيت وانا بقرا ولا لا 


output reg       o_tx_en,
output reg [3:0] o_tx_mode,
output reg       o_rx_en,
output reg [3:0] o_rx_mode,
output reg       o_frmcnt_en,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [4:0] o_regf_addr,
output reg       o_engine_abort,  // هيطلع بواحد لما يحصل ابورت 
output reg       o_engine_done    // هيطلع بواحد لما ابعت كل الداتا وبعدها ال س ار س بشكل طبيعي
);

// tx modes needed  
localparam [2:0]  tx_idle = 'b000,
                  Reserved_preamble = 'b001,
                  special_preamble_tx = 'b010,
                  one_preamble = 'b011,
                  zero_preamble = 'b100,
				          Serializing_byte = 'b101,
                  Calculating_Parity ='b110,
                  token_CRC = 'b111,
				  			  
 // rx modes neede 
localparam [3:0]     rx_idle = 'b0000,
                     preamble = 'b0001,
                     special_preamble_rx = 'b0010, 
                     Deserializing_byte = 'b0011,
                     Deserializing_dummy_byte = 'b0100, 
                     Check_token = 'b0101,
                     Check_Parity_value = 'b0110,
                     CRC_received = 'b0111,
                     Error = 'b1000;

// fsm states
localparam [3:0]    idle = 'b0000,
                    first_stage_command_Pre = 'b0001,
                    command_word = 'b0010,
					          address = 'b0011,               // broadcast or dierecet 
					          parity = 'b0100,
					          sec_stage_first_data_pre = 'b0101,             // sent by controller
					          ack_waiting = 'b0110,
					          first_data_byte = 'b0111,
					          second_data_byte = 'b1000,
					          third_stage_first_data_pre = 'b1001,             // send by target or controller
					          abort_bit = 'b1010,                      //   aborting by controller or target             
					          fourth_stage_crc_first_pre = 'b1011,
					          fourth_stage_crc_second_pre = 'b1100,
					          token_crc_bits = 'b1101,                 // 4 bits
					          crc_value_bits = 'b1110,                  // 5 bits 
					          error = 'b1111;
					
wire parity_data ;					
                  
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
   
  o_tx_en = 'b0 ; 
  o_rx_en = 'b0 ;
	o_rx_mode = rx_idle ;
  o_frmcnt_en = 'b0 ;
  o_regf_wr_en = 'b0 ;
  o_regf_rd_en = 'b0 ;
  o_engine_done = 'b0 ;
	o_regf_addr = 'b0;
  
  
  case(current_state)
  
  idle : begin 
          
		  o_tx_mode = tx_idle ;

		  end
		  
		 		  		  
  first_stage_command_Pre :  begin
           
		   o_tx_en = 'b1 ;
		   o_tx_mode = special_preamble_tx ;
   
		   end 
           		   
	
  command_word	: begin 
    
		  o_tx_en = 'b1;
		  o_tx_mode = Serializing_byte ; 
		  o_regf_addr = ; 
		  o_regf_rd_en = 'b1 ;
		  
            end 
            
  
  address : begin 
    
      o_tx_en = 'b1;
		  o_tx_mode = Serializing_byte ;
		  o_regf_addr = ; 
		  o_regf_rd_en = 'b1 ;
		  parity_data = 'b0;  
		  
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
       o_tx_mode = Serializing_byte;
  		   o_regf_addr = // undetermined yet0 
		   o_regf_rd_en = 'b1 ;
      end
       
     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_byte ;
	     o_regf_addr = // undetermined yet0 
		   o_regf_wr_en = 'b1 ;
	    end 

             end
             
             
  second_data_byte        : begin
    
	 parity_data = 'b1;

   if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_byte;
  		   o_regf_addr = // undetermined yet0 
		   o_regf_rd_en = 'b1 ;
      end
       
     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_byte ;
	     o_regf_addr = // undetermined yet0 
		   o_regf_wt_en = 'b1 ;
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
          if (!i_engine_ter)  
            begin
              o_tx_en = 'b1;
              o_tx_mode = one_preamble; // لو مش هترمنيت هبعت وان 
            end
          else
            begin
              o_tx_en = 'b1;
              o_tx_mode = zero_preamble;  // لو هترمنيت هبعت زيرو 
            end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;
		  
		  if(!i_rx_pre)       //////////////   ابورت من التارجت
		  o_engine_abort = 'b1;
		  else 
		  o_engine_abort = 'b0;

         end



             end 


  fourth_stage_crc_first_pre     : begin
    
    if (i_regf_wr_rd_bit)
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
             
             
 fourth_stage_crc_second_pre     : begin
    
    if (i_regf_wr_rd_bit)
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
             
   
   token_crc_bits        : begin

    if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
          o_tx_mode = token_CRC;
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = Check_token;
         end


             end 			 

	
   crc_value_bits   : begin

    if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
          o_tx_mode =  CRC_checksum ;
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = CRC_received;
         end

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
		        
		        if (i_tx_mode_done) begin
		          next_state = parity ;
				  
				  end
		        else
		          next_state = address ;
		          
            end 
            
            
		      parity	: begin 
		        
		 if (i_rx_mode_done | i_tx_mode_done)
		   begin
				
				if (parity_data)	
				 begin		 
				   
				  if (!i_regf_wr_rd_bit)
				    begin
				      
				     if(!i_frmcnt_last)
		           next_state = third_stage_first_data_pre ;
				     else 
				       next_state = fourth_stage_first_crc_pre ;
					   
					 end
				       
				    
				  else begin
				  
				  if (i_rx_error) //////////////////
				    next_state = error;
				  else 
				    next_state = third_stage_first_data_pre;
					
					end
				      
				    end
				      
				
				else 
				  next_state =  sec_stage_first_data_pre ;
				  
				 end
				  
				 
		  else
		    next_state = parity ;
		          
            end
            
            
 		      sec_stage_first_data_pre	: begin 
		        
		        if (i_tx_mode_done)
		           next_state = ack_waiting ;
				  
		        else
		         next_state = sec_stage_first_data_pre ;
		          
            end
            
          
  		       ack_waiting	: begin 
		        
		        if (i_rx_mode_done)
				
				if (!i_rx_error)        ///////////////////
		          next_state = first_data_byte ;
				else 
                  next_state = error ;				
		        else
		          next_state = ack_waiting ;
		          
            end 
            
            
 		  first_data_byte	: begin 
		        
		        if (i_rx_mode_done | i_tx_mode_done)
		
				      next_state = second_data_byte ;

			   else
		          next_state = first_data_byte ;
		          
            end
            
            
     second_data_byte	: begin 
		        
		        if (i_rx_mode_done | i_tx_mode_done)
				next_state = parity;
				else 				
		          next_state = second_data_byte ;
		          
            end

       
			third_stage_first_data_pre : begin 
			  
			
				if (i_rx_mode_done | i_tx_mode_done)
				  begin
				   if(i_regf_wr_rd_bit)
				     begin
				       
				       if (i_rx_pre)
		               next_state = abort_bit ; ////////////
		              else
                       next_state = fourth_stage_crc_second_pre ;
                 
             
                  else
                  next_state = abort_bit ;
             
             end
              
		        else
		          next_state = third_stage_first_data_pre ;
		          
		       end
		       
		     end
			
			
			
			abort_bit : begin
			 if(i_rx_mode_done | i_tx_mode_done)
			   begin
			
			  		if (!i_regf_wr_rd_bit)
				    begin
				      
				     if(i_rx_pre)
		           next_state = first_data_byte ;
				     else 
				       next_state = idle ;
				       
				    end
				       
				    
				  else
				    begin
				      
				     if(i_engine_ter) //// انبوت هيقولي انا عايز اترمنيت ولا لا 
		           next_state = idle ;
				     else 
				       next_state = first_data_byte ;
				      
				    end 
				    
				 else
				   next_state = abort_bit ;
				   
		end

			
			
			fourth_stage_first_crc_pre : begin 
			  
			    if (i_rx_mode_done | i_tx_mode_done)
		          next_state = fourth_stage_second_crc_pre ;  // 
		        else
		          next_state = fourth_stage_first_crc_pre ;
				  
			end
			
			
			fourth_stage_second_crc_pre : begin 
			  
			    if (i_rx_mode_done | i_tx_mode_done)
		          next_state = token_crc_bits ;  // 
		        else
		          next_state = fourth_stage_second_crc_pre ;
				  
			end
				  
				  
			token_crc_bits : begin 
				if (i_rx_mode_done | i_tx_mode_done)
		          next_state = crc_value_bits ;  // 
		        else
		          next_state =  token_crc_bits ;
				  
			end
			
			crc_value_bits : begin 
			  
			 if (i_rx_mode_done | i_tx_mode_done)
		       next_state = idle ;  // 
		   else
		       next_state = crc_value_bits ;	  
				  
			end
			
			
			error : begin 
			 
			 if (i_rx_mode_done)
		       next_state = idle ;  // 
		   else
		       next_state = error ;	
			
			end 
			

			  
     endcase
   end
       

endmodule
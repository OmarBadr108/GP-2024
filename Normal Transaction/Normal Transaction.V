module ddr_mode (
input        i_sys_clk,
input        i_sys_rst,
input        i_engine_en,
input        i_frmcnt_last,
input        i_tx_mode_done,
input        i_tx_parity_data,
input        i_rx_mode_done,
input        i_rx_pre,
input        i_regf_wr_rd_bit,
input        i_rx_error,
input        i_regf_toc,
input        i_regf_dev_index,

/*// to be removed 
input  [4:0] i_bitcount,  
input        i_scl_pos_edge,                 // for testbench
input        i_scl_neg_edge,*/


output reg       o_tx_en,
output reg [4:0] o_tx_mode,
output reg       o_rx_en,
output reg [3:0] o_rx_mode,
output reg       o_frmcnt_en,
output reg       o_bitcnt_en, // added
output reg       o_bitcnt_rst, // rst the counter due to error 
output reg       o_sdahand_pp_od,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [9:0] o_regf_addr,
output reg [3:0] o_sclstall_no_of_cycles,
output reg       o_sclstall_en,
output reg       o_regf_abort,  
output reg       o_engine_done,
output reg [1:0] o_regf_error_type

);  




// types of error  
localparam [1:0]  frame_error = 'b00,
                  parity_error = 'b10,
                  NACK = 'b10,
                  CRC_error = 'b01;


// timing specification   
localparam [3:0]  restart_stalling = 'd8,
                  exit_stalling = 'd11;


// tx modes needed  
localparam [3:0]  Serializing_command_word = 'b0000,
                  Serializing_address = 'b0001,              
                  special_preamble_tx = 'b0010,  //01
                  one_preamble = 'b0101,   // send 1 in pp or od 
                  zero_preamble = 'b0100,  // send zero
				  Serializing_first_byte = 'b0101, 
				  Serializing_second_byte = 'b1010, 
                  Calculating_Parity_Command ='b0111,
				  Calculating_Parity_Data ='b1000,
				  CRC_value = 'b1001,
                  token_CRC = 'b1010,
                  Restart_Pattern = 'b1011,
                  Exit_Pattern = 'b1100;

 // rx modes needed 
localparam [3:0]     
		     preamble = 'b001, 
                     nack_bit = 'b010 ,				 
                     Deserializing_byte = 'b011,                   
                     Check_token = 'b100,
                     Check_Parity_value = 'b101,
                     Check_CRC_value = 'b110,
                     Error = 'b111;
                     

// fsm states
localparam [4:0]              idle = 'b00000,
                              first_stage_command_Pre = 'b00001,
                              command_word = 'b00010,
					          address = 'b00011,               // broadcast or dierecet 
					          parity = 'b00100,
					          sec_stage_first_data_pre = 'b00101,             // sent by controller
					          ack_waiting = 'b00110,
					          first_data_byte = 'b00111,
					          second_data_byte = 'b01000,
					          third_stage_first_data_pre = 'b01001,             // send by target or controller
					          abort_bit = 'b01010,                      //   aborting by controller or target             
					          fourth_stage_crc_first_pre = 'b01011,
					          fourth_stage_crc_second_pre = 'b01100,
					          token_crc_bits = 'b01101,                 // 4 bits
					          crc_value_bits = 'b01110,                  // 5 bits 
					          error = 'b1111,
					          restart = 'b10000,
					          exit = 'b10001;


reg    [4:0]         current_state,
                     next_state ;
					 
reg [6:0] target_addres;

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
  o_frmcnt_en = 'b0 ;
  o_regf_wr_en = 'b0 ;
  o_regf_rd_en = 'b0 ;
  o_engine_done = 'b0 ;
	o_regf_addr = 'b0;
	o_regf_abort = 'b0;
	o_sclstall_en = 'b0;
	o_sclstall_no_of_cycles = 'b0;
	o_sdahand_pp_od = 'b1;
	o_bitcnt_en = 'b1; //
	o_bitcnt_rst = 'b0;


  case(current_state)

  idle : begin 

		   o_tx_en = 'b0 ;
           o_bitcnt_en = 'b0;		   

		  end


  first_stage_command_Pre :  begin

		   o_tx_en = 'b1 ;
		   o_tx_mode = special_preamble_tx ;
		   

		   end 


  command_word	: begin 

		  o_tx_en = 'b1;
		  o_tx_mode = Serializing_command_word ; 

            end 


  address : begin 

          o_tx_en = 'b1;
		  o_tx_mode = Serializing_address ;
		  o_regf_addr = target_addres;

		  end


  parity        : begin

        if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
		  
		  if (i_tx_parity_data)
          o_tx_mode = Calculating_Parity_Data;
		  else 
		  o_tx_mode = Calculating_Parity_Command;
	  
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = Check_Parity_value;
          if (i_rx_error)
            o_regf_error_type = parity_error;
          else
            o_regf_error_type = 0; 
         end

             end 


 sec_stage_first_data_pre : begin 

      o_tx_en = 'b1;
      o_tx_mode = one_preamble ;
	  o_sdahand_pp_od = 'b0; // open drain
	  

             end 


  ack_waiting : begin

          o_rx_en = 'b1 ;
	      o_rx_mode = nack_bit ;
	      if (i_rx_error)
         o_regf_error_type = NACK;
        else
         o_regf_error_type = 0;
		 
		   if (!i_regf_wr_rd_bit)
		   o_regf_addr = 'd1;
		   else
           o_regf_addr = 'd10;		   
		   

             end 


  first_data_byte : begin

    if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_first_byte; 		    
	   o_regf_rd_en = 'b1 ;
      end

     else
      begin
           o_rx_en = 'b1 ;
	       o_rx_mode = Deserializing_byte ;
		   o_regf_wr_en = 'b1 ;
	    end 
		
		
		
 if (i_tx_mode_done | i_rx_mode_done)    // for increasing address to be ready 
  o_regf_addr = o_regf_addr + 'd1;       /// reserved addr should be considered
  else
   o_regf_addr = o_regf_addr + 'd0;

             end


  second_data_byte        : begin
   
  if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_second_byte;  		    
		o_regf_rd_en = 'b1 ;
      end

     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_byte ;
		   o_regf_wr_en = 'b1 ;
	    end 

	 end


  third_stage_first_data_pre    : begin

        if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
          o_tx_mode = one_preamble;
		      o_sdahand_pp_od = 'b0;  // open drain
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

          end

        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;

		  if(!i_rx_pre)  
		  o_regf_abort = 'b1;
		  else 
		  o_regf_abort = 'b0;

         end

             end 


fourth_stage_crc_first_pre     : begin
    
    if (!i_regf_wr_rd_bit)
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
          o_tx_mode =  CRC_value ;
         end
    else
         begin

          o_rx_en = 'b1;
          o_rx_mode = Check_CRC_value;
          if (i_rx_error)
            o_regf_error_type = CRC_error;
          else
            o_regf_error_type = 0;

         end

             end 


   error   : begin

          o_rx_en = 'b1;
          o_rx_mode = Error;
		  o_bitcnt_rst = 'b1 ;//added
		  

             end


   restart   : begin

          o_tx_en = 'b1;
          o_tx_mode = Restart_Pattern;
          o_engine_done = 'b1;
          o_sclstall_no_of_cycles = restart_stalling;
          o_sclstall_en = 'b1;
		  o_bitcnt_rst = 'b1 ; //added

             end


   exit   : begin

          o_tx_en = 'b1;
          o_tx_mode = Exit_Pattern;
          o_engine_done = 'b1;
          o_sclstall_no_of_cycles = exit_stalling;
          o_sclstall_en = 'b1;
		  o_bitcnt_rst = 'b1 ; //added

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

				    if (i_tx_parity_data)begin	
				          		 

				           if (!i_regf_wr_rd_bit)
				             begin

				               if(!i_frmcnt_last)
		                     next_state = third_stage_first_data_pre ;
				               else 
				                 next_state = fourth_stage_crc_first_pre ;

					        end


				           else begin

				            if (i_rx_error) 
				             next_state = error;
				             
				            else 
				              
				             begin
				 
				            if(!i_frmcnt_last)
		                   next_state = third_stage_first_data_pre ;
				            else 
				               next_state = fourth_stage_crc_first_pre ;
				               
					           end
				   

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
		          begin
				
				       if (!i_rx_error)      
		             next_state = first_data_byte ;
				    else 
                 next_state = error ;
                 
               end
               				
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
		               next_state = abort_bit ; 
		             else
                   next_state = fourth_stage_crc_second_pre ;
                   
             end
                 
             
            else
              next_state = abort_bit ;
             
             end
              
		     else
		       next_state = third_stage_first_data_pre ;
		       
		     end


			abort_bit : begin
			 if(i_rx_mode_done | i_tx_mode_done)
			   begin
			
			  		if (!i_regf_wr_rd_bit)
				    begin
				      
				     if(i_rx_pre)
		           next_state = first_data_byte ;
				     else
				      begin 
				        
				       if (i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;
				        
				      end
				       
				    end
				       
				    
				  else
				    begin
				      
				     if(i_frmcnt_last) 
				       
		          begin 
				        
				       if (!i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;
				        
				      end
		           
				     else 
				       next_state = first_data_byte ;
				      
				    end 
				    
			end
				    
				 else
				   next_state = abort_bit ;
				   
		end



			fourth_stage_crc_first_pre : begin 
			  
			    if (i_rx_mode_done | i_tx_mode_done)
		          next_state = fourth_stage_crc_second_pre ;  
		        else
		          next_state = fourth_stage_crc_first_pre ;
				  
			end
			
			
			fourth_stage_crc_second_pre : begin 
			  
			    if (i_rx_mode_done | i_tx_mode_done)
		          next_state = token_crc_bits ;  
		        else
		          next_state = fourth_stage_crc_second_pre ;
				  
			end


			token_crc_bits : begin 
				if (i_rx_mode_done | i_tx_mode_done)
		          next_state = crc_value_bits ;  
		        else
		          next_state =  token_crc_bits ;

			end

			crc_value_bits : begin 

			 if (i_rx_mode_done | i_tx_mode_done)

		       			begin 

				       if (!i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;

				      end 

		   else
		       next_state = crc_value_bits ;	  

			end


			error : begin 

			 if (i_rx_mode_done)

		       		 begin 

				       if (!i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;

				      end

		   else
		       next_state = error ;	

			end


			restart :  begin

		        if (i_tx_mode_done)
		          next_state = first_stage_command_Pre ;
		        else
		          next_state = restart ;

		  end 


			exit :  begin

		        if (i_tx_mode_done)
		          next_state = idle ;
		        else
		          next_state = exit ;

		  end 

     endcase
   end
   
   
   always@(*) begin
    case (i_regf_dev_index)                     
        5'd0 : target_addres = 7'd8  ;
        5'd1 : target_addres = 7'd9  ;
        5'd2 : target_addres = 7'd10 ;
        5'd3 : target_addres = 7'd11 ;

        5'd4 : target_addres = 7'd12 ;
        5'd5 : target_addres = 7'd13 ;
        5'd6 : target_addres = 7'd14 ;
        5'd7 : target_addres = 7'd15 ;

        5'd8 : target_addres = 7'd16 ;
        5'd9 : target_addres = 7'd17 ;
        5'd10: target_addres = 7'd18 ;
        5'd11: target_addres = 7'd19 ;

        5'd12: target_addres = 7'd20 ;
        5'd13: target_addres = 7'd21 ;
        5'd14: target_addres = 7'd22 ;
        5'd15: target_addres = 7'd23 ;

        5'd16: target_addres = 7'd24 ;
        5'd17: target_addres = 7'd25 ;
        5'd18: target_addres = 7'd26 ;
        5'd19: target_addres = 7'd27 ;

        5'd20: target_addres = 7'd28 ;
        5'd21: target_addres = 7'd29 ;
        5'd22: target_addres = 7'd30 ;
        5'd23: target_addres = 7'd31 ;

        5'd24: target_addres = 7'd32 ;
        5'd25: target_addres = 7'd33 ;
        5'd26: target_addres = 7'd34 ;
        5'd27: target_addres = 7'd35 ;

        5'd28: target_addres = 7'd36 ;
        5'd29: target_addres = 7'd37 ;
        5'd30: target_addres = 7'd38 ;
        5'd31: target_addres = 7'd39 ;
    endcase

end 




endmodule

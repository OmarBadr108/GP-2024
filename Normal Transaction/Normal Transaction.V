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

output reg       o_tx_en,
output reg [3:0] o_tx_mode,
output reg       o_rx_en,
output reg [3:0] o_rx_mode,
output reg       o_frmcnt_en,
output reg       o_bitcnt_en, // added
output reg       o_bitcnt_rst, // rst the counter due to error 
output reg       o_sdahand_pp_od,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [4:0] o_regf_addr,
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
localparam [3:0]  Serializing_command_word = 'b000,
                  Serializing_address = 'b1010,              
                  special_preamble_tx = 'b001,  //01
                  one_preamble = 'b010,   // send 1 in pp or od 
                  zero_preamble = 'b011,  // send zero
				          Serializing_byte = 'b100, 
				          Calculating_Parity ='b101,  //////////////////////////////////////////////
				          CRC_value = 'b0111,
                  token_CRC = 'b111,
                  Restart_Pattern = 'b1000,
                  Exit_Pattern = 'b1001;

 // rx modes needed 
localparam [3:0]     special_preamble_rx = 'b0010, 
					           preamble = 'b010, 
                     nack_bit = 'b001 ,				 
                     Deserializing_byte = 'b0011,                   
                     Check_token = 'b0101,
                     Check_Parity_value = 'b0110,
                     Check_CRC_value = 'b0111,
                     Error = 'b1000;
                     

// fsm states
localparam [4:0]    idle = 'b0000,
                    first_stage_command_Pre = 'b0001,
                    command_word = 'b0010,
					address = 'b0011,               // broadcast or dierecet 
					parity = 'b0100,
					sec_stage_first_data_pre = 'b0101,             // sent by controller
					ack_waiting = 'b0110,
					data = 'b0111, ////////////////////////////////////////////////////////////////////////
					third_stage_first_data_pre = 'b1001,             // send by target or controller
					abort_bit = 'b1010,                      //   aborting by controller or target             
					fourth_stage_crc_first_pre = 'b1011,
					fourth_stage_crc_second_pre = 'b1100,
					token_crc_bits = 'b1101,                 // 4 bits
					crc_value_bits = 'b1110,                  // 5 bits 
					error = 'b1111,
					restart = 'b10000,
					exit = 'b10001;


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

		  end


  parity  : begin

        if (!i_regf_wr_rd_bit)
         begin
           
          o_tx_en = 'b1;
          o_tx_mode = Calculating_Parity; ////////////////////////////////////

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

             end 


  data : begin ////////////////////////////

    if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_byte;
  		   o_regf_addr = 0; // undetermined yet0 
		   o_regf_rd_en = 'b1 ;
      end

     else
      begin
       o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_byte ;
	     o_regf_addr = 0; // undetermined yet0 
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
		             next_state = data ; ///////////////////////
				    else 
                 next_state = error ;
                 
               end
               				
		        else
		          next_state = ack_waiting ;
		          
            end 


 		data	: begin /////////////////////

		        if (i_rx_mode_done | i_tx_mode_done)
				      next_state = third_stage_first_data_pre ;

			      else
		          next_state = data ;

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
		           next_state = data ;
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
				       next_state = data ; /////////////////
				      
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


endmodule

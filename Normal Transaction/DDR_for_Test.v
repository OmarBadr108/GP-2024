module ddr_mode (

input        i_sys_clk,
input        i_sys_rst,
input        i_engine_en,
input        i_frmcnt_last,
input        i_tx_mode_done,
//input        i_tx_parity_data,
input        i_rx_mode_done,
input        i_rx_pre,
input        i_rx_error,

//----------- interface input signals-----------//

input        i_regf_toc,          	// 1’b0: RESTART ; 1’b1: STOP
input [4:0]  i_regf_dev_index,   	// 5’b0: Broadcat  ;  any other value: Direct  
input        i_regf_short_read,  	// 1’b0: ALLOW_SHORT_READ  ; 1’b1: SHORT_READ_IS_ERROR 
input        i_regf_wroc ,       	//1’b0: NOT_REQUIRED RESPONSE ; 1’b1: REQUIRED RESPONSE
input        i_regf_wr_rd_bit,   	//  1’b0: WRITE ; 1’b1: READ
input        i_regf_cmd_attr,     	// 1'b1: Immediate Data Transfer Command ; 1'b0:Regular Transfer Command
input [2:0]  i_regf_dtt,			// Determine The Number of Data Byte


/*// to be removed 
input  [4:0] i_bitcount,  
input        i_scl_pos_edge,                 // for testbench
input        i_scl_neg_edge,*/


output reg       o_tx_en,
output reg [3:0] o_tx_mode,
output reg       o_rx_en,
output reg [3:0] o_rx_mode,
output reg       o_frmcnt_en,
output reg       o_bitcnt_en, 
output reg       o_bitcnt_rst,  
output reg       o_sdahand_pp_od,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [9:0] o_regf_addr,
output reg [3:0] o_sclstall_no_of_cycles,
output reg       o_sclstall_en,  
output reg       o_engine_done,
output reg [7:0] o_tx_special_data,

//------------ interface output signals ---------//
output reg       o_regf_abort,
output reg [3:0] o_regf_error_type

);  




//------------- types of error ------------//
localparam [3:0]    SUCCESS = 'd0,
                    CRC_Error = 'd1,
                    Parity_Error = 'd2,
					Frame_Error = 'd3,
					Address_Header_Error = 'd4,
					NACK_Error = 'd5,
                    OVL_Error = 'd6,                // not used
                    I3C_SHORT_READ_Error = 'd7, 
                    HC_ABORTED_Error  = 'd8,       // by Controller due to internal error (not used)
					BUS_ABORTED_Error = 'd9 ;       // Aborted due to Early Termination, or Target not completing read or write of data phase of transfer









//------------ timing specification ------------//  
localparam [3:0]  restart_stalling = 'd8,
                  exit_stalling = 'd11;











//--------------- tx modes -------------//   
localparam [3:0]  seven_zeros = 'd0,
                  Serializing_address = 'd1,              
                  special_preamble_tx = 'd2,  //01
                  one_preamble = 'd3,   // send 1 in pp or od 
                  zero_preamble = 'd4,  // send zero
				  Serializing_byte = 'd5, 
				 /* Serializing_second_byte = 'b1010,*/ 
                  Calculating_Parity ='d6,
				  /*Calculating_Parity_Data ='b1000,*/
				  CRC_value = 'd7,
                  token_CRC = 'd8,
                  Restart_Pattern = 'd9,
                  Exit_Pattern = 'd10;
				
				//  Read_Write_bit = 'b1010;

 
 
 
 
 
 
 
 
 // -------------- rx modes ----------------//  
localparam [3:0]     preamble = 'd0, 
                  //   nack_bit = 'd1 ,				 
                     Deserializing_byte = 'd3,                   
                     Check_token = 'd4,
                     Check_Parity_value = 'd5,
                     Check_CRC_value = 'd6,
                     Error = 'd7;
                     









//------------------ fsm states ----------------//
localparam [4:0]              idle = 'd0,
                              first_stage_command_Pre = 'd1,
                              serializing_seven_zeros = 'd2,
					          address = 'd3,                
					          parity = 'd4,
					          sec_stage_first_data_pre = 'd5,             // sent by controller
					          ack_waiting = 'd6,
					          first_data_byte = 'd7,
					          second_data_byte = 'd8,
					          third_stage_first_data_pre = 'd9,             // send by target or controller
					          abort_bit = 'd10,                      //   aborting by controller or target             
					          fourth_stage_crc_first_pre = 'd11,
					          fourth_stage_crc_second_pre = 'd12,
					          token_crc_bits = 'd13,                 // 4 bits
					          crc_value_bits = 'd14,                  // 5 bits 
					          error = 'd15,
					          restart = 'd16,
					          exit = 'd17,
							  Read_Write_bit = 'd18,
							  serializing_zeros = 'd19;


//------------------ internal signals decleration -----------------//					 
reg [6:0] target_addres,broadcast_address;
reg    [4:0]         current_state , next_state ;
/*wire [3:0] count ;*/
reg parity_data, Parity_data_seq ;


localparam specific_address = 'd 1000; // for 8 zeros


//--------------------------- 1: Sequential Always Block ------------------------------//
always @(posedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
     current_state <= idle ;
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
	o_bitcnt_en = 'b1; 
	o_bitcnt_rst = 'b0;
	o_sclstall_no_of_cycles <= 'b0;
    o_sclstall_en <= 'b0;
    o_regf_abort <= 'b0;
	o_regf_error_type <= SUCCESS;  // No error
	
   end
  else
   begin
     current_state <= next_state ;
   end
 end







//--------------------------- 2: Combinational Always Block For FSM States------------------------------//
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
		          next_state = Read_Write_bit ;
		        else
		          next_state = first_stage_command_Pre ;

		          end


		      Read_Write_bit	: begin 

		        if (i_tx_mode_done)
		          next_state = serializing_seven_zeros ;
		        else
		          next_state = Read_Write_bit ;

		          end
				  
				  
				  
			  serializing_seven_zeros	: begin 

		        if (i_tx_mode_done)
		          next_state = address ;
		        else
		          next_state = serializing_seven_zeros ;

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

				    if (Parity_data_seq)begin	
				          		 

				           if (!i_regf_wr_rd_bit)
				             begin

				               if(!i_frmcnt_last)
		                     next_state = third_stage_first_data_pre ;
				               else 
				                 next_state = fourth_stage_crc_first_pre ;

					        end


				           else begin

				            if (i_rx_error)             // may no sync due to delay one system clk cycle
				             next_state = error;
				             
				            else 
				              
				             begin
				 
				           /* if(!i_frmcnt_last)
		                   next_state = third_stage_first_data_pre ;
				            else 
				               next_state = fourth_stage_crc_first_pre ;*/
				               
							   next_state = third_stage_first_data_pre ;
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
				
				       if (i_rx_pre)      
		             next_state = first_data_byte ;
				    else 
                 next_state = error ;
                 
               end
               				
		        else
		          next_state = ack_waiting ;
		          
            end 


 		first_data_byte	: begin 

		        if (i_rx_mode_done | i_tx_mode_done) begin 
					
					if (!i_frmcnt_last)
				      next_state = second_data_byte ;
					else  
					 next_state = serializing_zeros;
					 
				end

			      else
		          next_state = first_data_byte ;

            end
			
		serializing_zeros	: begin 

		        if (i_rx_mode_done | i_tx_mode_done) 
										 
				    next_state = parity ;
					
			      else
		          next_state = serializing_zeros ;

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
						 begin
						   if ((!i_frmcnt_last) && i_regf_short_read )  
					        next_state = error ;  // target didn't send all requierd data 
					       else 
					        next_state = fourth_stage_crc_second_pre ;
                        end
                   
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
				        
				      /* if (i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;*/
						
						next_state = error;    // target aborts writing
				        
				      end
				       
				    end
				       
				    
				  else
				    begin
				      
				     if(i_frmcnt_last) 
				       
		          begin 
				        
				      /* if (!i_regf_toc)
				        next_state = restart ;
				       else
				        next_state = exit ;*/
						next_state = error;     // Controller aborts reading
						
				        
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
		          next_state = idle ;  // return to idle waitng to be enabled
		        else
		          next_state = restart ;

		  end 


			exit :  begin

		        if (i_tx_mode_done)
		          next_state = idle ;
		        else
		          next_state = exit ;

		  end 
		  
		  
		/*  parity_0	: begin 

		        if (i_rx_mode_done | i_tx_mode_done)
		          begin

				    next_state = parity_1

		  else
		    next_state = parity_0 ;

            end
			
			parity_1	: begin 

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
		    next_state = parity_1 ;

            end*/

     endcase
   end








//--------------------------- 3: Combinational Always Block For Outputs------------------------------//
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
	o_bitcnt_en = 'b1; 
	o_bitcnt_rst = 'b0;
	o_regf_abort <= 'b0;
	o_regf_error_type <= SUCCESS;  // No error


  case(current_state)

  idle : begin 

		   o_tx_en = 'b0 ;
           o_bitcnt_en = 'b0;		   

		  end


  first_stage_command_Pre :  begin


		   o_tx_en = 'b1 ;
		   o_tx_mode = special_preamble_tx ;  //01
		   o_frmcnt_en = 'b1 ;
		   

		   end 


  Read_Write_bit	: begin 

		  o_tx_en = 'b1;
		  o_frmcnt_en = 'b1 ;
			if(!i_regf_wr_rd_bit)
		 o_tx_mode = zero_preamble;
		 else 
		 o_tx_mode = one_preamble;


            end 
			
			
			
  serializing_seven_zeros	: begin         // command first byte {Read_Write_bit,serializing_seven_zeros}

		  o_tx_en = 'b1;
		  o_tx_mode = seven_zeros ; 
		   o_frmcnt_en = 'b1 ;

            end 


  address : begin                            // command second byte {address,par_adj"calc by Tx"}

         
		  o_tx_en = 'b1;
		  o_tx_mode = Serializing_address ;
		   o_frmcnt_en = 'b1 ;
		
		  parity_data = 'b0;                  // Calculating_Parity_Command
		
		
		if (!i_regf_dev_index)
		o_regf_addr = broadcast_address;      // sending in broadcast mode   
        else 
		o_regf_addr = target_addres;          // sending in Direct mode 

		  end


  parity        : begin

		if (i_tx_mode_done)
		 o_frmcnt_en = 'b1 ;
		 else 
		  o_frmcnt_en = 'b0 ;

	   if (!i_regf_wr_rd_bit)
         begin
          o_tx_en = 'b1;
		  
		  /*if (i_tx_parity_data)
          o_tx_mode = Calculating_Parity_Data;         
		  else 
		  o_tx_mode = Calculating_Parity_Command;     */
		  
		   o_tx_mode = Calculating_Parity;           // Calculating Parity for command and data
		  
	  
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = Check_Parity_value;         //check the parity correctness
          
		  if (i_rx_error)
            o_regf_error_type = Parity_Error;
          else
            o_regf_error_type = SUCCESS; 
         end

             end 


 sec_stage_first_data_pre : begin   // 1

      o_tx_en = 'b1;
      o_tx_mode = one_preamble ;
	  o_sdahand_pp_od = 'b0; // open drain , which makes a change in scl line //to be edited
	  

             end 


  ack_waiting : begin
	     
		// o_sdahand_pp_od = 'b0;   //listening to sda
          o_rx_en = 'b1 ;
	      o_rx_mode = preamble ;
	      if (!i_rx_pre)
         o_regf_error_type = NACK_Error;
        else 
		begin
         o_regf_error_type = SUCCESS;	
		 o_tx_en = 1;                      // preparing enable for next state 
		 end
		   
		   
		 if (!i_regf_wr_rd_bit)
		  if (i_regf_cmd_attr)              // Immediate Transfer
			begin 
			case (i_regf_dtt)
			'd0 : o_regf_addr = 'd0;         // no data 
			'd1 : o_regf_addr = 'd20;       // sending Byte1 of address 'd20 
			'd2 : o_regf_addr = 'd20;       // sending Byte1 of address 'd20 and  sending Byte2 of address 'd21
			'd3 : o_regf_addr = 'd20;		// sending Byte1 of address 'd20 and sending Byte2 of address 'd21 and sending Byte3 of address 'd22
			'd4 : o_regf_addr = 'd20;		// sending Byte1 of address 'd20 and sending Byte2 of address 'd21 and sending Byte3 of address 'd22 and sending Byte3 of address 'd23
			'd5 : o_regf_addr = 'd0;        // only defining byte and no data
			'd6 : o_regf_addr = 'd21;       // sending defining byte and sending Byte2 of address 'd21
			'd7 : o_regf_addr = 'd21;		// sending defining byte and sending Byte2 of address 'd21 and sending Byte3 of address 'd22
			endcase
			end
		else                              // Regular Transfer
			begin 
			o_regf_addr = 'd1;      // starting from this address to write Regular data
			end 
		   else
           o_regf_addr = 'd10;		// starting from this address to read  Regular data
		   

             end 


  first_data_byte : begin
     
	 o_frmcnt_en = 'b1 ;

    if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_byte; 		    
	   o_regf_rd_en = 'b1 ;
      end

     else
      begin
         o_rx_en = 'b1 ;
	     o_rx_mode = Deserializing_byte ;
		 o_regf_wr_en = 'b1 ;
		 //o_sdahand_pp_od = 'b0;   //listening to sda
	    end 
		
		
	/*if (!i_frmcnt_last) 
		count_en = 'd0;
	else 
		count_en = 'd1;*/
		
		
		
	if (i_tx_mode_done | i_rx_mode_done) begin     // for increasing address to be ready 
		
		if (!i_frmcnt_last)
		o_regf_addr = o_regf_addr + 'd1;
		else
		o_regf_addr = specific_address;
		
		end
	
	
	else
		o_regf_addr = o_regf_addr + 'd0;

             end
			 
			 
	serializing_zeros : begin            // state of dummy data in case of odd number of bytes
	  o_frmcnt_en = 'b1 ;
	
	if (!i_regf_wr_rd_bit) 
	  begin 
	   o_tx_en = 'b1;
       o_tx_mode = Serializing_byte;
	   end
	else
	  begin
		o_rx_en = 'b1 ;
	    o_rx_mode = Deserializing_byte ;
	  end
	   
	   

	
      parity_data = 'b1;                  // Calculating Parity of Data
     end 	   
	 
	


  second_data_byte        : begin
   
   parity_data = 'b1;                   // Calculating Parity of Data
   o_frmcnt_en = 'b1 ;
  
  if (!i_regf_wr_rd_bit)
      begin
       o_tx_en = 'b1;
       o_tx_mode = Serializing_byte;  		    
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
		   o_sdahand_pp_od = 'b0;  // open drain , listening to sda
         end
        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;
		  
		  if (i_rx_mode_done)
		  begin 
				if (!i_rx_pre)
				begin
					 if ((!i_frmcnt_last) && i_regf_short_read ) 
					o_regf_error_type = I3C_SHORT_READ_Error ;  // target didn't send all requierd data 
					else 
					o_regf_error_type = SUCCESS ;
				end
				else 
				o_regf_error_type = SUCCESS ;
				
			end 
			else 
			o_regf_error_type = SUCCESS ;
			
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
			  o_regf_abort <= 'b0;
	          o_regf_error_type <= BUS_ABORTED_Error;  // Controller aborts reading
            end

          end

        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;

		  if(!i_rx_pre)  
		  begin 
		  o_regf_abort = 'b1;
		  o_regf_error_type <= BUS_ABORTED_Error;   // target aborts writing 
		  end
		  
		  else 
		  o_regf_abort = 'b0;

         end

             end 
			 
			 
			 
		/*	 second_data_byte        : begin
   
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

	 end*/


fourth_stage_crc_first_pre     : begin
    
   /* if (!i_regf_wr_rd_bit)
         begin*/
        
		o_tx_en = 'b1;
        o_tx_mode = zero_preamble;
         
		 /*end
          else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;
         end*/

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
		  

		  if ( i_rx_mode_done)		  
		  begin      		  
			if (i_rx_pre)
			o_regf_error_type = SUCCESS ;
			else 
			o_regf_error_type = Frame_Error ;          // error due to pre = 00 
		  
         end
		 else  
		 o_regf_error_type = SUCCESS ;

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
		  
		  if (i_rx_error)
            o_regf_error_type = Frame_Error;
          else
            o_regf_error_type = SUCCESS;
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
            o_regf_error_type = CRC_Error;
          else
            o_regf_error_type = SUCCESS;

         end

             end 


   error   : begin

          o_rx_en = 'b1;
          o_rx_mode = Error;
		  o_bitcnt_rst = 'b1 ;
		  
		  

             end


   restart   : begin

          o_tx_en = 'b1;
          o_tx_mode = Restart_Pattern;
          o_sclstall_no_of_cycles = restart_stalling;
          o_sclstall_en = 'b1;
		  o_bitcnt_rst = 'b1 ;
        
		if(i_tx_mode_done)
		 o_engine_done = 'b1;		  

             end


   exit   : begin

          o_tx_en = 'b1;
          o_tx_mode = Exit_Pattern;
          o_sclstall_no_of_cycles = exit_stalling;
          o_sclstall_en = 'b1;
		  o_bitcnt_rst = 'b1 ; 
		  
		  
		  if(i_tx_mode_done)
		 o_engine_done = 'b1;		  

             end            

      endcase
    end


   
   //--------------------------- 4: Combinational Always Block For Encoding The Address------------------------------//
   always@(*) begin
    case (i_regf_dev_index)                     
        5'd0 : broadcast_address =     7'd8  ;  // for broadcast 
        5'd1 : target_addres     =     7'd9  ;
        5'd2 : target_addres     =     7'd10 ;
        5'd3 : target_addres     =     7'd11 ;

        5'd4 : target_addres     =     7'd12 ;
        5'd5 : target_addres     =     7'd13 ;
        5'd6 : target_addres     =     7'd14 ;
        5'd7 : target_addres     =     7'd15 ;

        5'd8 : target_addres     =     7'd16 ;
        5'd9 : target_addres     =     7'd17 ;
        5'd10: target_addres     =     7'd18 ;
        5'd11: target_addres     =     7'd19 ;

        5'd12: target_addres     =     7'd20 ;
        5'd13: target_addres     =     7'd21 ;
        5'd14: target_addres     =     7'd22 ;
        5'd15: target_addres     =     7'd23 ;

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
/**********************************************/
/*reg [3:0] count_seq ;

always@ (posedge i_sys_clk or negedge i_sys_rst)
begin
if (!i_sys_rst)
count_seq <= 'd0;  
else 
count_seq <= count; 
end*/

//--------------------------- 5: Sequential Always Block ------------------------------//
always@ (posedge i_sys_clk or negedge i_sys_rst)
begin
if (!i_sys_rst)
Parity_data_seq <= 'd0;  
else 
Parity_data_seq <= parity_data; 
end


endmodule







module bits_counter(
    input  wire       i_sys_clk             ,
    input  wire       i_rst_n               ,
    input  wire       i_bitcnt_en           ,  
    input  wire       i_scl_pos_edge        ,  
    input  wire       i_scl_neg_edge        ,  
    output reg  [4:0] o_cnt_bit_count 
    );

// COUNTER CORE

always @(posedge i_sys_clk or negedge i_rst_n) begin 
    if(~i_rst_n) begin
        o_cnt_bit_count <= 0 ;
    end 
    else begin 
        if (i_bitcnt_en) begin 
            if (i_scl_neg_edge || i_scl_pos_edge) begin 
                if (o_cnt_bit_count == 5'd20) begin 
                    o_cnt_bit_count <= 5'd0 ;                     // from 0 to 19 it won't reach 20 
                end
                else begin 
                    o_cnt_bit_count <= o_cnt_bit_count + 1 ; 
                end  
            end 
        end 
        else begin 
            o_cnt_bit_count <= 5'd0 ;
        end 
    end
end
endmodule 

module scl_generation(
    input  wire       i_sdr_ctrl_clk          ,   // 50 MHz clock
    input  wire       i_sdr_ctrl_rst_n        ,
    input  wire       i_sdr_scl_gen_pp_od     ,   // 1: Push-Pull      // 0: for Open-Drain
    input  wire       i_scl_gen_stall         ,  // 1 for stalling
    input  wire       i_sdr_ctrl_scl_idle     ,
    input  wire       i_timer_cas             ,
    output reg        o_scl_pos_edge          ,
    output reg        o_scl_neg_edge          ,
    output reg        o_scl                  );


//-- states encoding in gray ---------------------------------------------

localparam LOW  = 1'b0 ;
localparam HIGH = 1'b1 ;


//-- internal wires declaration -------------------------------------------

reg          state   ;  //assigned at fsm
reg  [6:0]   count   ;  //assigned at counter
reg          switch  ;  //assigned at counter


//-- scl generation fsm ---------------------------------------------------

always @(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
  begin: scl_generation_fsm

    if (!i_sdr_ctrl_rst_n)
      begin
        //-- state
          state   <=  HIGH   ;
        //-- outputs
          o_scl   <=  1'b1  ;
          o_scl_pos_edge <= 1'b0;
          o_scl_neg_edge <= 1'b0;
      end

    else
      begin
        case (state)
          LOW:
            begin
                o_scl_neg_edge <= 1'b0;
               if (i_scl_gen_stall) state <=   LOW  ;
               else
                begin
                    if (switch)
                      begin
                        o_scl <=   1'b1 ;
                        state <=   HIGH ;
                        o_scl_pos_edge <= 1'b1;
                      end
                    else
                      begin
                        o_scl <=   1'b0 ;
                        state <=   LOW  ;
                        o_scl_pos_edge <= 1'b0;
                      end
                end
            end

          HIGH:
            begin
            o_scl_pos_edge <= 1'b0;
                if ((switch && !i_sdr_ctrl_scl_idle) || (i_timer_cas) )
                  begin
                    o_scl <=   1'b0 ;
                    state <=   LOW  ;
                    o_scl_neg_edge <= 1'b1;
                  end
                else
                  begin
                    o_scl <=   1'b1 ;
                    state <=   HIGH ;
                    o_scl_neg_edge <= 1'b0;
                  end
            end
        endcase
      end
  end
//-- switch generation counter --------------------------------------------

always @(posedge i_sdr_ctrl_clk or negedge i_sdr_ctrl_rst_n)
  begin: scl_generation_counter

    if (!i_sdr_ctrl_rst_n)
      begin
          count  <= 7'b1 ;
          switch <= 1'b0 ;
      end

  // 50 MHz/4 = 12.5 MHz for Push-Pull
    else if (i_sdr_scl_gen_pp_od)
      begin
          if (count >= 7'd2)
            begin
              count  <= 7'b1 ;
              switch <= 1'b1 ;
            end
          else
            begin
              count  <= count + 1'b1 ;
              switch <= 1'b0 ;
            end
      end

  // 50 MHz/125 = 400 KHz for Open-Drain
    else
      begin
          if (count == 7'd62)
            begin
              switch <= 1'b1;
              count <= count + 1'b1;
            end
          else if (count == 7'd125)
            begin
              count  <= 7'b1 ;
              switch <= 1'b1;
            end
          else
            begin
              count <= count + 1'b1;
              switch <= 1'b0;
            end
      end

  end



endmodule


module RX (

input                     i_sys_clk,
input                     i_sys_rst,
input                     i_sclgen_scl,
input                     i_sclgen_scl_pos_edge,
input                     i_sclgen_scl_neg_edge,
input                     i_ddrccc_rx_en,
input                     i_sdahnd_rx_sda,
input     [4:0]           i_bitcnt_rx_bit_count,
input     [3:0]           i_ddrccc_rx_mode,
input     [4:0]               i_crc_value,
input                     i_crc_valid,

output  reg  [7:0]        o_regfcrc_rx_data_out,
output  reg               o_ddrccc_rx_mode_done,
output  reg               o_ddrccc_pre,
output  reg               o_ddrccc_error,
output  reg               o_crc_en,                 
output  reg               o_crc_data_valid
);








/////////////////////////////////rx modes/////////////////////////////////
localparam [3:0]     
                     PREAMBLE            = 'd0  ,            
                     DESERIALIZING_BYTE  = 'd3  ,                   
                     CHECK_TOKEN         = 'd4 ,
                     CHECK_PAR_VALUE     = 'd5  ,
                     CHECK_CRC_VALUE     = 'd6  ;
                     



////////////////////////////////////////////////////////////////////////////


reg [2:0]  count;
wire        count_done;
reg [15:0] data_paritychecker;
reg        byte_num;

reg [7:0] o_regfcrc_rx_data_out_temp;
reg [3:0] token_value_temp;
reg [1:0] parity_value_temp;
reg [4:0] CRC_value_temp;
wire [1:0] parity_value_calc;

wire SCL_edges; 

//////////////////////////////parity calc////////////////////////////////////

 assign parity_value_calc[1] =  data_paritychecker[15]^data_paritychecker[13]^data_paritychecker[11]^data_paritychecker[9]^data_paritychecker[7]^data_paritychecker[5]^data_paritychecker[3]^data_paritychecker[1] ;     
 assign parity_value_calc[0] =  data_paritychecker[14]^data_paritychecker[12]^data_paritychecker[10]^data_paritychecker[8]^data_paritychecker[6]^data_paritychecker[4]^data_paritychecker[2]^data_paritychecker[0]^1'b1 ; 


assign count_done = (count==7)? 1'b1:1'b0 ;

assign SCL_edges = (i_sclgen_scl_pos_edge || i_sclgen_scl_neg_edge);


////////////////////////////// Registering data bytes for parity check ////////////////////////////////////

/*
always @(*)  
begin
   if ((byte_num == 0) && (count_done))
    data_paritychecker[15:8] = o_regfcrc_rx_data_out_temp;
   else if ((byte_num == 1) &&  (count_done))
    data_paritychecker[7 :0]  = o_regfcrc_rx_data_out_temp;
   //else
   //data_paritychecker = 0; ////////////////////////////to be revisit 


end
*/
always @(posedge i_sys_clk or negedge i_sys_rst)  
begin
  if(!i_sys_rst)

  begin
    data_paritychecker <= 'b0;
  end

  else if ((byte_num == 0) && (count_done))
   data_paritychecker[15:8] = o_regfcrc_rx_data_out_temp;

  else if ((byte_num == 1) &&  (count_done))
   data_paritychecker[7 :0]  = o_regfcrc_rx_data_out_temp;


end






always @(posedge i_sys_clk or negedge i_sys_rst) 
begin

  if (!i_sys_rst) 
   begin

    o_regfcrc_rx_data_out <= 8'd0;  
    o_ddrccc_rx_mode_done <= 1'b0;
    o_ddrccc_pre          <= 1'bz; //should be editted
    o_ddrccc_error        <= 1'b0;
    o_crc_en              <= 1'b0;   
    count                 <= 'b0;
    byte_num              <= 1'b0;
    o_crc_data_valid      <=  'b0;
   // parity_value_temp     <= 1'b0;
   end


  else if (i_ddrccc_rx_en) 
   begin
    o_regfcrc_rx_data_out <= 8'd0;  
    o_ddrccc_rx_mode_done <= 1'b0;
    //o_ddrccc_pre          <= 1'bz;   //should be editted
    o_ddrccc_error        <= 1'b0;
    o_crc_en              <= 1'b0; 
    //rx_mode_done_flag     <= 1'b0;
   // parity_value_temp     <= 1'b0;
    o_crc_data_valid      <= 1'b0;

   case(i_ddrccc_rx_mode) 

    PREAMBLE :          begin
                          count                   <= 'b0;
                         if (SCL_edges)
                          begin
                           //o_ddrccc_pre          <= i_sdahnd_rx_sda;
                           //o_ddrccc_rx_mode_done <= 1'b1;
                           //rx_mode_done_flag     <= 1'b1;
                           byte_num               <= 1'b0;
                           count                  <= 'b0;
                          end
                          else 
                          begin
                            o_ddrccc_rx_mode_done <= 1'b1;
                            o_ddrccc_pre          <= i_sdahnd_rx_sda;
                            end
                        end


      DESERIALIZING_BYTE: begin
                            
                            o_ddrccc_rx_mode_done <= 1'b0;
                            o_ddrccc_pre <= 'bz;
                            o_crc_data_valid <= 'b0;
                            o_crc_en         <=  1'b1;
                            
                            if(SCL_edges)
                               begin
                          
                                count <= count + 1; 
                                if(count == 'd7)
                                begin
                                  count <= 'b0;
                                  o_crc_data_valid <= 1'b1;
                                  o_regfcrc_rx_data_out <= o_regfcrc_rx_data_out_temp;
                                  byte_num <= 'b1;
                                end
                               end

                            else 
                             begin
                              o_ddrccc_rx_mode_done <= 1'b0;
                              o_regfcrc_rx_data_out_temp['d7 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd7)                    
                               begin
                                  
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                end

                            end
                          end



    CHECK_TOKEN :       begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;

                         if(SCL_edges)
                          begin
                            count <= count + 1'b1;
                            
                            if(count == 'd3)
                              begin
                               
                                count <= 'b0; 

                               if(token_value_temp != 4'hC)
                                  o_ddrccc_error<=1'b1;
                                else
                                  o_ddrccc_error<=1'b0;
                                  

                              end 
                          
                          end

                          else 
                          begin
                              token_value_temp['d3 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd3)
                                o_ddrccc_rx_mode_done <= 1'b1;
                            
                          end
                        end 
 
    CHECK_PAR_VALUE :    /*  begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;
                         parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;
                         if(SCL_edges)
                          begin
                           parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;                       
                          end
                         else if(count == 'd1)
                                begin
                                  count<=0;
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  //count <= 'b0; 
                                  if(parity_value_calc != parity_value_temp)
                                    o_ddrccc_error<=1'b1;
                                  else
                                    o_ddrccc_error<=1'b0;
                                end 
                         

                          else 
                            begin
                             count <= count + 1'b1;

                              
                              //o_ddrccc_rx_mode_done <= 1'b0; 
                            end
                        end*/
                        begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;

                         if(SCL_edges)
                          begin
                           parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;

                             
                          end
                          else  if(count == 'd1)
                                begin
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  count <= 'b0; 
                                  if(parity_value_calc != parity_value_temp)
                                    o_ddrccc_error<=1'b1;
                                  else
                                    o_ddrccc_error<=1'b0;
                                end 
                          else 
                            begin
                              count <= count + 1'b1;
                               parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;
                              //o_ddrccc_rx_mode_done <= 1'b0; 
                            end
                        end 
 
 
 
    CHECK_CRC_VALUE :   begin

                         //count <= 'b0;
                         o_crc_en<=1'b1;

                         if(SCL_edges)
                           begin
                              count <= count + 1'b1;   
                              
                              if(count == 'd4)
                                begin
                                 count <= 'b0;
                                 if(i_crc_valid)
                                 begin
                                  if(CRC_value_temp!= i_crc_value)
                                     o_ddrccc_error<=1'b1;
                                  else
                                     o_ddrccc_error<=1'b0;
                                 end
                                 end 
                           end
                          
                          else 
                           begin
                           CRC_value_temp['d4 - count] <= i_sdahnd_rx_sda;
                           if(count == 'd4)
                                  o_ddrccc_rx_mode_done <= 1'b1;
                           
                           end
                         
                        end
 
 
 
 
    default:     begin
                 o_regfcrc_rx_data_out <= 8'd0;  
                 o_ddrccc_rx_mode_done <= 1'b0;
                 o_ddrccc_pre          <= 1'b0; //////////////////////////
                 o_ddrccc_error        <= 1'b0;
                 o_crc_en              <= 1'b0; 
                 o_crc_data_valid      <= 1'b0;        
                 end

   
  endcase
 end
end
endmodule

module frame_counter(
    //input  wire  [7:0] i_fcnt_no_frms     ,
    input  wire        i_fcnt_clk         ,
    input  wire        i_fcnt_rst_n       ,
    input  wire        i_fcnt_en          ,
    input  wire        i_regf_CMD_ATTR    ,     // HDR 1 bit only selects bit [0] (1 for immediate and 0 for regular)
    input  wire [15:0] i_regf_DATA_LEN    ,     // HDR 
    input  wire [2:0]  i_regf_DTT         ,     // HDR
    input  wire [4:0]  i_cnt_bit_count    ,     // HDR
    input  wire        i_Direct_Broadcast_n ,     // HDR  1 for direct and 0 for Broadcast    
    output reg         o_cccnt_last_frame       // HDR
    );

reg [15:0] count = 16'd0 ;
//wire       count_done   ;

    always @(posedge i_fcnt_clk or negedge i_fcnt_rst_n) begin 
        if (!i_fcnt_rst_n) begin 
            o_cccnt_last_frame = 1'b0 ;
            count              = 16'd0 ;
        end 
        else begin 
            if(i_fcnt_en) begin 
                if (count == 16'd0) begin 
                    o_cccnt_last_frame = 1'b1 ;
                    // stay here for 20 bits
                end 
                else begin 
                    if (i_cnt_bit_count == 'd9 || i_cnt_bit_count == 'd19) begin 
                        count = count - 1 ;
                    end 

                end 
            end 
            else begin                                      // Disabled to load the count value
                if (i_Direct_Broadcast_n) begin               // Direct
                    if (!i_regf_CMD_ATTR) begin             // regular 
                        count = i_regf_DATA_LEN + 5 ;       // 8 + 8 + CRC word + RESTART + 8 
                    end 
                    else begin                              // immediate 
                        case (i_regf_DTT) 
                            3'd0 : count = 1 ;
                            3'd1 : count = 6 ;
                            3'd2 : count = 7 ;
                            3'd3 : count = 8 ;
                            3'd4 : count = 9 ;

                            3'd5 : count = 1 ;
                            3'd6 : count = 6 ;
                            3'd7 : count = 7 ;
                        endcase 
                    end 
                end 

                else begin                                  // Broadcast
                    if (!i_regf_CMD_ATTR) begin             // regular 
                        count = i_regf_DATA_LEN + 1 ; 
                    end 
                    else begin                              // immediate 
                        case (i_regf_DTT) 
                            3'd0 : count = 1 ;
                            3'd1 : count = 2 ;
                            3'd2 : count = 3 ;
                            3'd3 : count = 4 ;
                            3'd4 : count = 5 ;

                            3'd5 : count = 1 ;
                            3'd6 : count = 2 ;
                            3'd7 : count = 3 ;
                        endcase
                    end 
                end
            end 
        end 
    end 

endmodule 

module tx (
input        i_sys_clk,
input        i_sys_rst,
input        i_ddrccc_tx_en,
input        i_sclgen_scl_pos_edge,
input        i_sclgen_scl_neg_edge,
input [3:0]  i_ddrccc_tx_mode,
input [7:0]  i_regf_tx_parallel_data, 
input [7:0]  i_ddrccc_special_data, // special from ddr or ccc (address or ccc value)  
input [4:0]  i_crc_crc_value, //separate calculation of crc (of what serialized) in another block 

output reg        o_sdahnd_serial_data, //SDA
output reg        o_ddrccc_mode_done,
output reg        o_crc_en, 
output reg [7:0]  o_crc_parallel_data //sending byte byte of what serialized for crc block
);


// tx modes needed  
localparam [3:0]  special_preambles = 'b0000, //2'b01 
                  serializing_address = 'b0001, //address of target
    				          serializing_zeros = 'b0011 ,  //7-zeros in the first byte of cmd word        
                  one = 'b0010, // for representing preamble bit or reading_or_writing bit  
                  zero = 'b0110, // for representing preamble bit or reading_or_writing bit
				          serializing_data = 'b0111, //data byte from reg to be serialized
				          CCC_value = 'b0101 , //special data in case of transmitting CCC
				          calculating_Parity = 'b0100, //parity of word serialized either cmd word or data word
				          token_CRC = 'b1100, //special bits 4'b1100
				          CRC_value = 'b1101, //CRC value arrived of data serialized
                  restart_Pattern = 'b1111,
                  exit_Pattern = 'b1110;

/*****special values****/			  
reg [1:0] special_preamble = 'b01 ;
reg [3:0] token = 4'b1100;

/***internal signals****/
wire parity_adj; 
wire [7:0] A; //CMD_Word_Second_Byte
wire P1, P0; //parity bits to be serialized
wire P1_cmdword, P0_cmdword; //parity bits of cmdword
wire P1_data, P0_data; //parity bits of data
wire [1:0] P;
reg [7:0] D1, D2; //first_and_second_Data_Bytes


/***helpful flags****/
integer counter;
integer value;
reg reset_counter_flag;
reg rd_wr_flag; //storing rd_or_wr bit for calculating (parity adj) and (cmd word parity)
reg parity_flag; //to distinguish parity is calculated for cmd or data
reg first_byte_full; //to distinguish tx is serializing first byte or second byte


assign A = {i_ddrccc_special_data[6:0],parity_adj} ; 
assign parity_adj = ( rd_wr_flag ^ (^i_ddrccc_special_data) ) ;
assign P1 = (parity_flag)? P1_data : P1_cmdword ; 
assign P0 = (parity_flag)? P0_data : P0_cmdword ;
assign P = {P1,P0} ;
assign P1_cmdword = rd_wr_flag ^ A[7] ^ A[5] ^ A[3] ^ A[1] ;
assign P0_cmdword = A[6] ^ A[4] ^ A[2] ^ A[0] ^ 1 ;
assign P1_data = D1[7] ^ D1[5] ^ D1[3] ^ D1[1] ^ D2[7] ^ D2[5] ^ D2[3] ^ D2[1] ;
assign P0_data = D1[6] ^ D1[4] ^ D1[2] ^ D1[0] ^ D2[6] ^ D2[4] ^ D2[2] ^ D2[0] ^ 1 ; 


 always @ (posedge i_sys_clk or negedge i_sys_rst)
	begin 

		if(~i_sys_rst) begin 
		    o_sdahnd_serial_data<= 1;
        o_ddrccc_mode_done<= 0;
        o_crc_parallel_data<= 0;
        o_crc_en<= 0;
		    counter <= 0;
		    reset_counter_flag <= 0;
		    value <= 0;
		    parity_flag <= 0;
		    first_byte_full <= 0;
		    o_crc_en <= 0; 
		end 

		else if (i_ddrccc_tx_en) begin

		o_ddrccc_mode_done <= 0;

		case (i_ddrccc_tx_mode)

		  ///////////////////////

		serializing_zeros : begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		    o_sdahnd_serial_data <= 1'b0 ;    
		    if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
          end

			  else
			    begin
			     if ( counter == 'd5 )
			      o_ddrccc_mode_done <= 'b1;
			     counter <= counter + 1;
			    end

			 end

			else if ( counter == 'd6 )
			  begin
			 reset_counter_flag <= 0;
			 value <= 6;
			 end

		  end

		/////////////////////////////////

		one : begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin

		     if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= 1;
       			 if ( counter == 'd0 )
			       o_ddrccc_mode_done <= 'b1;
          end
			 end

			else if ( counter == 'd0 )
			  begin
			 rd_wr_flag <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 0;
			 end
		  end

		  ////////////////////////////

		 zero : begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		     if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
   		      o_sdahnd_serial_data <= 0;
 		       if ( counter == 'd0 )
			       o_ddrccc_mode_done <= 'b1;
          end
			 end

			else if ( counter == 'd0 )
			  begin
			 rd_wr_flag <= 'b0;
			 reset_counter_flag <= 0;
			 value <= 0;
			 end
		  end

		  /////////////////////////////////////

		special_preambles : begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin

		    if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= special_preamble['d1] ;
          end

			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= special_preamble['d0 - counter] ;
			    if ( counter == 'd0 )
			       o_ddrccc_mode_done <= 'b1;
			    end

			 end

			else if ( counter == 'd1 )
			  begin
			 reset_counter_flag <= 0;
			 value <= 1;
			 end

		 end	
		 ////////////////////////////////////

		 CCC_value :  begin

		  o_crc_en <= 'b1;
			o_crc_parallel_data <= i_ddrccc_special_data;
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= i_ddrccc_special_data['d7] ;
           end

			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= i_ddrccc_special_data['d6 - counter] ;
			    if ( counter == 'd6 )
			       o_ddrccc_mode_done <= 'b1;
			    end
			 end

	 else if ( counter == 'd7 )
			begin
			 reset_counter_flag <= 0;
			 value <= 7;
			 parity_flag <= 1;
			 if (!first_byte_full)
			   begin
			    D1 <= i_ddrccc_special_data;
			    first_byte_full <= 1;
			   end
			 else
			   begin
			    D2 <= i_ddrccc_special_data;
			    first_byte_full <= 0;
			   end
		  end

	 end	

		 ///////////////////////////////////

		serializing_data :  begin

		  o_crc_en <= 'b1;
			o_crc_parallel_data <= i_regf_tx_parallel_data;
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= i_regf_tx_parallel_data['d7] ;
           end

			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= i_regf_tx_parallel_data['d6 - counter] ;
			    if ( counter == 'd6 )
			      o_ddrccc_mode_done <= 'b1;
			    end
			 end

	 else if ( counter == 'd7 )
			begin
			 reset_counter_flag <= 0;
			 value <= 7;
			 parity_flag <= 1;
			 if (!first_byte_full)
			   begin
			    D1 <= i_regf_tx_parallel_data;
			    first_byte_full <= 1;
			   end
			 else
			   begin
			    D2 <= i_regf_tx_parallel_data;
			    first_byte_full <= 0;
			   end
		  end

	 end	

	 /////////////////////////////

		serializing_address :  begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= A['d7] ;
           end

			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= A['d6 - counter] ;
			    if ( counter == 'd6 )
			      o_ddrccc_mode_done <= 'b1;
			    end

			 end

			else if ( (counter == 'd7) )
			  begin
			 reset_counter_flag <= 0;
			 value <= 7;
			 end

		 end	

		 /////////////////////////////////


		 calculating_Parity : begin

		   if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin

		     if ( (counter == value) & (!reset_counter_flag))
		     begin
          counter <= 'd0;
          reset_counter_flag <= 1;
          o_sdahnd_serial_data <= P[1];
         end
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= P[(0 - counter)];
			    if ( counter == 'd0 )
			      o_ddrccc_mode_done <= 'b1;
			    end

			 end

			else if ( counter == 1 )
			 begin
			  reset_counter_flag <= 0;
			  value <= 1;
			 end

		 end	  


		 /////////////////////////////////

		token_CRC :	 begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin

		    if ( (counter == value) & (!reset_counter_flag))
		     begin
          counter <= 'd0;
          reset_counter_flag <= 1;
          o_sdahnd_serial_data <= token[3];
         end
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= token[(2 - counter)];
			    if ( counter == 'd2 )
			      o_ddrccc_mode_done <= 'b1;
			    end

			 end

			else if ( counter == 3 )
			  begin
			 reset_counter_flag <= 0;
			 value <= 3;
			 end

		 end	 

		/////////////////////////////////////////

		CRC_value :  begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if ( (counter == value) & (!reset_counter_flag))
		       begin
		        o_sdahnd_serial_data <= i_crc_crc_value[4];
            counter <= 'd0;
            reset_counter_flag <= 1;  
           end
			   else
			     begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= i_crc_crc_value[(3 - counter)];
			    if ( counter == 'd3 )
			      o_ddrccc_mode_done <= 'b1;
			    end
			  end

			else if ( counter == 'd4 )
			 begin
			  reset_counter_flag <= 0;
			  value <= 4;
			 end

	  end

			  /////////////////////////////////////////////

		restart_Pattern: begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if ( (counter == value) & (!reset_counter_flag))
		       begin
		        o_sdahnd_serial_data <= 1;
            counter <= 'd0;
            reset_counter_flag <= 1; 
           end

			   else
			    begin
			     counter <= counter + 1;
			     o_sdahnd_serial_data <= !o_sdahnd_serial_data;
			     if ( counter == 'd2 )
			      o_ddrccc_mode_done <= 'b1;
			    end	  
			  end

	    else if ( counter == 'd3 )
			 begin
			  reset_counter_flag <= 0;
			  value <= 3;
			 end
		  end

			  ////////////////////////////////////////////

			exit_Pattern: begin

		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if ( (counter == value) & (!reset_counter_flag))
		       begin
		        o_sdahnd_serial_data <= 1;
            counter <= 'd0;
            reset_counter_flag <= 1; 
           end

			   else
			    begin
			     counter <= counter + 1;
			     o_sdahnd_serial_data <= !o_sdahnd_serial_data;
			     if ( counter == 'd5 )
			      o_ddrccc_mode_done <= 'b1;
			    end	  
			  end

	    else if ( counter == 'd6 )
			 begin
			  reset_counter_flag <= 0;
			  value <= 7;
			 end
		  end

		////////////////////////////////////////////////

		endcase
		end		

		else
		  begin
		 	  o_sdahnd_serial_data<= 1;
        o_ddrccc_mode_done<= 0;
        o_crc_parallel_data<= 0;
        o_crc_en<= 0;
		    counter <= 0;
		    reset_counter_flag <= 0;
		    value <= 0;
		    end

		end



	endmodule




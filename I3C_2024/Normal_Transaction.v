module DDR_NT (

input        i_sys_clk,
input        i_sys_rst,
input        i_engine_en,
input        i_frmcnt_last,
input        i_tx_mode_done,
//input        i_tx_parity_data,
input        i_rx_mode_done,
input        i_rx_pre,
input        i_rx_error,
input        i_staller_done,

//----------- interface input signals-----------//

input        i_regf_toc,          	// 1’b0: RESTART ; 1’b1: STOP
input [4:0]  i_regf_dev_index,   	// 5’b0: Broadcast  ;  any other value: Direct  
input        i_regf_short_read,  	// 1’b0: ALLOW_SHORT_READ  ; 1’b1: SHORT_READ_IS_ERROR 
input        i_regf_wroc ,       	//1’b0: NOT_REQUIRED RESPONSE ; 1’b1: REQUIRED RESPONSE
input        i_regf_wr_rd_bit,   	//  1’b0: WRITE ; 1’b1: READ
input [2:0]  i_regf_cmd_attr,     	// 1'b1: Immediate Data Transfer Command ; 1'b0:Regular Transfer Command
input [2:0]  i_regf_dtt,			// Determine The Number of Data Byte
input [5:0]  i_bitcnt ,


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
//output reg       o_bitcnt_stop, 
output reg       o_sdahand_pp_od,
output reg       o_regf_wr_en,
output reg       o_regf_rd_en,
output reg [11:0] o_regf_addr,
output reg [4:0] o_sclstall_no_of_cycles,
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
localparam [4:0]  restart_stalling = 'd10,
                  exit_stalling = 'd16;











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
							  serializing_zeros = 'd19,
							  waiting = 'd20 ;


//------------------ internal signals decleration -----------------//					 
reg [6:0] target_addres,broadcast_address;
reg    [4:0]         current_state , next_state ;
/*wire [3:0] count ;*/
reg parity_data, Parity_data_seq ,sysclk_done,en_sysclk ;


localparam specific_address = 'd 1000; // for 8 zeros


//--------------------------- 1: Sequential Always Block ------------------------------//
always @(posedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
     current_state <= idle ;
     o_tx_en = 'b0 ; //laila
  /*  o_tx_en = 'b0 ; 
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
	o_bitcnt_en = 'b0; 
	o_bitcnt_rst = 'b0;
	o_sclstall_no_of_cycles = 'b0;
    o_sclstall_en = 'b0;
    o_regf_abort = 'b0;
	o_regf_error_type = SUCCESS;  // No error*/
	
	
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
				
				       if (!i_rx_pre)      
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
					begin
						if (i_regf_wr_rd_bit)
						begin
							if (i_rx_pre)
								next_state = token_crc_bits ;
							else 
								next_state = error ;
						end
						
						else 
						next_state = token_crc_bits ;
						
						
					end
		        else
		          next_state = fourth_stage_crc_second_pre ;
				  
			end


			token_crc_bits : begin 
				if (i_rx_mode_done | i_tx_mode_done)
					begin
		          
					if (i_regf_wr_rd_bit)
					begin
						if (!i_rx_error)
							next_state = crc_value_bits ;
						else 
							next_state = error ;
					end
					
					else 
					next_state = crc_value_bits ;
					
					end
					
				  
				  
				   
		        else
		          next_state =  token_crc_bits ;

			end

			crc_value_bits : begin 

			 if (i_rx_mode_done | i_tx_mode_done)

		       	begin				
					if (i_regf_wr_rd_bit)
					begin
						
						if (!i_rx_error) 
						begin
							
							if (!i_regf_toc)
								next_state = restart ;
							else
								next_state = exit ;
						end 
						else 
							next_state = error ;
					end
					
					else
						begin
						

							if (!i_regf_toc)
								next_state = restart ;
							else
								next_state = exit ;
						 end
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

		        if (i_tx_mode_done /*&& i_staller_done*/)
		          next_state = idle ;  // return to idle waitng to be enabled
		        else
		          next_state = restart ;

		  end 


			exit :  begin

		        if (i_tx_mode_done /*&& i_staller_done*/)
		          next_state = idle ;
		        else
		          next_state = exit ;

		  end 
		  
		  
		  waiting :  begin 
		  
		  if (sysclk_done /*&& i_staller_done*/)
		          next_state = idle ;
		        else
		          next_state = waiting ;
		  
		  end
		  
		  
		  default : begin 
		  
		  next_state = idle ;
		  
			
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
  o_frmcnt_en = 'b1 ;
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
	o_regf_abort = 'b0;
	o_regf_error_type = SUCCESS;  // No error
	en_sysclk=0;
	o_tx_special_data = 'd0; 
	o_tx_mode = special_preamble_tx ;
	o_rx_mode = preamble ;
	parity_data ='d0;
//	o_bitcnt_stop = 'b0;


  case(current_state)

  idle : begin 

		   o_tx_en = 'b0 ;
           o_bitcnt_en = 'b0;
           o_frmcnt_en = 'b0 ;		   

		  end


  first_stage_command_Pre :  begin


		   o_tx_en = 'b1 ;
		   o_tx_mode = special_preamble_tx ;  //01
		   o_frmcnt_en = 'b0 ;
		   

		   end 


  Read_Write_bit	: begin 

		  o_tx_en = 'b1;
		  o_frmcnt_en = 'b0 ;
			if(!i_regf_wr_rd_bit)
		 o_tx_mode = zero_preamble;
		 else 
		 o_tx_mode = one_preamble;


            end 
			
			
			
  serializing_seven_zeros	: begin         // command first byte {Read_Write_bit,serializing_seven_zeros}

		  o_tx_en = 'b1;
		  o_tx_mode = seven_zeros ; 
		  o_frmcnt_en = 'b0 ;

            end 


  address : begin                            // command second byte {address,par_adj"calc by Tx"}

         
		  o_tx_en = 'b1;
		  o_tx_mode = Serializing_address ;
		   o_frmcnt_en = 'b1 ;
		
		  parity_data = 'b0;                  // Calculating_Parity_Command
		  en_sysclk ='b1;
		
		
		
		o_tx_special_data = target_addres;         
		
		end


  parity        : begin

		//if (i_tx_mode_done)
		 o_frmcnt_en = 'b1 ;
		/* else 
		  o_frmcnt_en = 'b0 ;*/

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
		  if (!Parity_data_seq)
		  begin
 		  o_tx_en = 'b1;
		  o_tx_mode = Calculating_Parity;
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

             end 


 sec_stage_first_data_pre : begin   // 

      o_tx_en = 'b1;
      o_tx_mode = one_preamble ;
	  
	 // o_sdahand_pp_od = 'b0; // open drain , which makes a change in scl line //to be edited
	  
     
             end 


  ack_waiting : begin
	     
		// o_sdahand_pp_od = 'b0;   //listening to sda
     
		
		en_sysclk=1;
		 o_frmcnt_en = 'b1 ;
		// wait (sysclk_done) ; // wait is unsynthesizable
   if(sysclk_done)
		begin
   		 o_rx_en = 'b1 ;
	      o_rx_mode = preamble ;
		 
		//  o_bitcnt_stop = 'b1;
		   
		 
		  
	      if ((!i_rx_pre) && i_rx_mode_done)
			begin
			o_regf_error_type = SUCCESS;
			o_tx_en = 'b1;
			o_tx_mode = Serializing_byte; 		    
			o_regf_rd_en = 'b1 ;
			end
        else 
		begin
         	
			o_regf_error_type = NACK_Error;
		
		 end
		   
		   
		 if (!i_regf_wr_rd_bit)
		 begin
		  if (i_regf_cmd_attr[0])              // Immediate Transfer
			begin 
			case (i_regf_dtt)
		//	'd0 : o_regf_addr = 'd0;         // no data 
			'd1 : o_regf_addr = 'd20;       // sending Byte1 of address 'd20 
			'd2 : o_regf_addr = 'd20;       // sending Byte1 of address 'd20 and  sending Byte2 of address 'd21
			'd3 : o_regf_addr = 'd20;		// sending Byte1 of address 'd20 and sending Byte2 of address 'd21 and sending Byte3 of address 'd22
			'd4 : o_regf_addr = 'd20;		// sending Byte1 of address 'd20 and sending Byte2 of address 'd21 and sending Byte3 of address 'd22 and sending Byte3 of address 'd23
		//	'd5 : o_regf_addr = 'd0;        // only defining byte and no data
		//	'd6 : o_regf_addr = 'd21;       // sending defining byte and sending Byte2 of address 'd21
		//	'd7 : o_regf_addr = 'd21;		// sending defining byte and sending Byte2 of address 'd21 and sending Byte3 of address 'd22
			endcase
			end
		 else                              // Regular Transfer			 
			o_regf_addr = 'd1;      // starting from this address to write Regular data
		  end 
		   else
           o_regf_addr = 'd10;		// starting from this address to read  Regular data
		  
		  
		  end
		  
	else 	   		
		o_rx_en = 'b0 ;

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
   en_sysclk ='b1;
  
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
		  // o_sdahand_pp_od = 'b0;  // open drain , listening to sda
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
			  o_regf_abort = 'b0;
	          o_regf_error_type = BUS_ABORTED_Error;  // Controller aborts reading
            end

          end

        else
         begin
          o_rx_en = 'b1;
          o_rx_mode = preamble;

		  if(!i_rx_pre)  
		  begin 
		  o_regf_abort = 'b1;
		  o_regf_error_type = BUS_ABORTED_Error;   // target aborts writing 
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
		if((i_bitcnt == 'd12) || (i_bitcnt == 'd11))
			begin 
			o_sclstall_en = 1;
			if(!i_regf_toc)
				o_sclstall_no_of_cycles = restart_stalling;
			else 
				o_sclstall_no_of_cycles = exit_stalling;
				
			end
		else 
			o_sclstall_en = 0;
         end
    else
         begin

          o_rx_en = 'b1;
          o_rx_mode = Check_CRC_value;
          
		 
		 if (i_rx_error)
            o_regf_error_type = CRC_Error;
          else
			begin 
				o_regf_error_type = SUCCESS;
					if((i_bitcnt == 'd12) || (i_bitcnt == 'd11))
						begin 
						o_sclstall_en = 1;
						if(!i_regf_toc)
							o_sclstall_no_of_cycles = restart_stalling;
						else 
							o_sclstall_no_of_cycles = exit_stalling;
						end
					else 
						o_sclstall_en = 0;
			end
			
			

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
		   

			if(i_tx_mode_done )
			 o_sclstall_en = 'b0;
		  else 
			o_sclstall_en = 'b1;
             end


   exit   : begin

          o_tx_en = 'b1;
          o_tx_mode = Exit_Pattern;
          o_sclstall_no_of_cycles = exit_stalling;
          o_sclstall_en = 'b1;
		 
			if(i_tx_mode_done )
			 o_sclstall_en = 'b0;
		  else 
			o_sclstall_en = 'b1;

             end     

	waiting : begin 
		o_sclstall_en = 'b0;
		o_tx_en = 'b1;
		if(i_regf_toc)
			o_tx_mode = Exit_Pattern;
		else 
			o_tx_mode = Restart_Pattern;
		en_sysclk =1 ;
		
		
		
		end
		
	

      endcase
    end


   
   //--------------------------- 4: Combinational Always Block For Encoding The Address------------------------------//
   always@(*) begin
		 
    case (i_regf_dev_index)                     
        5'd0 : target_addres =     7'd8  ;   
        5'd1 : target_addres     =     7'd9  ;  //0001001
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
	begin
	Parity_data_seq <= 'd0;  
	sysclk_done<=0;
	end
else 
	begin
	if (en_sysclk)
		begin
		sysclk_done<='b1;
		Parity_data_seq <= parity_data; 
		end
	else 
		sysclk_done<='b0;

//Parity_data_seq <= parity_data; 
	end
end

endmodule

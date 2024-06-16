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
input        i_crc_data_valid,
input        i_regf_read_n_write_bit,


output reg        o_sdahnd_serial_data, //SDA
output reg        o_ddrccc_mode_done,
output reg        o_crc_en, 
output reg [7:0]  o_crc_parallel_data ,//sending byte byte of what serialized for crc block
output reg        o_crc_last_byte,
output reg        o_crc_data_valid
);


// tx modes needed  
localparam [3:0]  special_preambles = 'b0000, 		//'d0			//2'b01 
                  serializing_address = 'b0001, 	//'d1			//address of target
    			  serializing_zeros = 'b0011 ,  	//'d3			//7-zeros in the first byte of cmd word        
                  one = 'b0010, 					//'d2			// for representing preamble bit or reading_or_writing bit  
                  zero = 'b0110, 					//'d6			// for representing preamble bit or reading_or_writing bit
				  serializing_data = 'b0111, 		//'d7			//data byte from reg to be serialized
				  CCC_value = 'b0101 , 				//'d5			//special data in case of transmitting CCC
				  calculating_Parity = 'b0100,  	//'d4			//parity of word serialized either cmd word or data word
				  token_CRC = 'b1100, 				//'d12			//special bits 4'b1100
				  CRC_value = 'b1101, 				//'d13			//CRC value arrived of data serialized
                  restart_Pattern = 'b1111,			//'d15
                  exit_Pattern = 'b1110;			//'d14


/**special values*/			  
reg [1:0] special_preamble = 'b01 ;
reg [3:0] token = 4'b1100;
reg [6:0] reserved =7'b0000000; //00//


/**internal signals*/
wire parity_adj; 
wire [7:0] A; //CMD_Word_Second_Byte
wire P1, P0; //parity bits to be serialized
wire P1_cmdword, P0_cmdword; //parity bits of cmdword
wire P1_data, P0_data; //parity bits of data
wire [1:0] P;
reg [7:0] D1, D2; //first_and_second_Data_Bytes
reg	crc_indicator ; //00//
reg [4:0] crc_temp ; //00//
reg [4:0] crc; //00//



/**helpful flags*/
integer counter;
reg reset_counter_flag;
reg rd_wr_flag; //storing rd_or_wr bit for calculating (parity adj) and (cmd word parity)
reg parity_flag; //to distinguish parity is calculated for cmd or data
reg first_byte_full; //to distinguish tx is serializing first byte or second byte
wire [3:0] tmp_restart ;


assign tmp_restart = 4'b 0101;
assign A = {i_ddrccc_special_data[6:0],parity_adj} ; 
assign parity_adj = ( rd_wr_flag ^ (^i_ddrccc_special_data) ) ;
assign P1 = (parity_flag)? P1_data : P1_cmdword ; 
assign P0 = (parity_flag)? P0_data : P0_cmdword ;
assign P = {P1,P0} ;
assign P1_cmdword = rd_wr_flag ^ A[7] ^ A[5] ^ A[3] ^ A[1] ;
assign P0_cmdword =  1 ;
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
		    parity_flag <= 0;
		    first_byte_full <= 0;
		    o_crc_en <= 0; 
		end 
		
		else if (i_ddrccc_tx_en) begin
		  
		o_ddrccc_mode_done <= 0;
		o_crc_data_valid <= 'b0;
		 o_crc_en <= 'b0;
		 o_crc_last_byte <= 'b0;
		
		case (i_ddrccc_tx_mode)
		  
		  ///////////////////////
		  
		serializing_zeros : begin
		  
		  o_crc_parallel_data <= {i_regf_read_n_write_bit , reserved};
		  o_crc_en <= 'b1;
		//	o_crc_data_valid <= 'b1;

		 if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		    o_sdahnd_serial_data <= 1'b0 ;    
		    if ( (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
		   o_crc_data_valid <= 'b1;
          end
          
			  else
			    begin
			     if ( counter == 'd5 ) begin 
			      o_ddrccc_mode_done <= 'b1;
				  end
			      counter <= counter + 1;
				 // o_crc_data_valid <= 'b0;
				 
				 
			    end
			    
			 end
			 
			else if ( counter == 'd6 )
			  begin
			 reset_counter_flag <= 0;
			 
			 end
		  
		  end
	
		/////////////////////////////////
		  
		one : begin
		  
		//	o_crc_en <= 'b1;
			o_crc_last_byte <= 'b0;
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		     
		     if (  (!reset_counter_flag) )
		      begin
           counter <= 0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= 1;
			     o_ddrccc_mode_done <= 'b1;
          end
			 end
			 
			else if ( counter == 'd0 )
			  begin
			 rd_wr_flag <= 'b1;
			 reset_counter_flag <= 0;
			 
			 end
		  end
		  
		  ////////////////////////////
		  
		 zero : begin
		//  o_crc_en <= 'b1;
			o_crc_last_byte <= 'b0;
		  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		     if ( (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
   		      o_sdahnd_serial_data <= 0;
			     o_ddrccc_mode_done <= 1;
          end
			 end
			 
			else if ( counter == 'd0 )
			  begin
			 rd_wr_flag <= 'b0;
			 reset_counter_flag <= 0;
			 
			 end
		  end
		  
		  /////////////////////////////////////
		
		special_preambles : begin
		 
		o_crc_last_byte <= 'b0;
		counter <= 'd0;   //editttt laila
		  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		        
		    if ( (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= special_preamble['d1] ; 
          end
          
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= special_preamble['d0 - counter] ;
			    if ( counter == 'd0 ) begin
			       o_ddrccc_mode_done <= 'b1;
				   parity_flag <= 0;  // to make P1=P1_cmd &P1=P0_cmd
				   end
			    end
			    
			 end
			 
			else if ( counter == 'd1 )
			  begin
			 reset_counter_flag <= 0;
			 
			 end
			 
		 end	
		 ////////////////////////////////////
		 
		/* CCC_value :  begin
		  
		  o_crc_last_byte <= 'b1;
		  o_crc_en <= 'b1;
		  crc_indicator <= 'b1;
		  crc_temp <= i_crc_crc_value ;

			
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if ((!reset_counter_flag) )
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
					begin
			       o_ddrccc_mode_done <= 'b1;
				   end
			    end
			 end
			 
	 else if ( counter == 'd7 )
			begin
			 reset_counter_flag <= 0;
			 
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
			 
	 end	*/
		
		 ///////////////////////////////////
		  		 
		 CCC_value :  begin
		  
		  o_crc_last_byte <= 'b0;
		  o_crc_en <= 'b1;
		  o_crc_parallel_data <= i_ddrccc_special_data;
			
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if ((!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= i_ddrccc_special_data['d7] ;
		   o_crc_data_valid <= 'b1;
           end
          
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= i_ddrccc_special_data['d6 - counter] ;
			    if ( counter == 'd6 )
					begin
			       o_ddrccc_mode_done <= 'b1;
				   end
			    end
			 end
			 
	 else if ( counter == 'd7 )
			begin
			 reset_counter_flag <= 0;
			 
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
			o_crc_last_byte <= 'b0;
			//o_crc_data_valid <= 'b1;
			
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if (  (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= i_regf_tx_parallel_data['d7] ;
		   o_crc_data_valid <= 'b1;
           end
          
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= i_regf_tx_parallel_data['d6 - counter] ;
			    if ( counter == 'd6 ) begin
			      o_ddrccc_mode_done <= 'b1;
				  end
				//  o_crc_data_valid <= 'b0;
			    end
			 end
			 
	 else if ( counter == 'd7 )
			begin
			 reset_counter_flag <= 0;
			 
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

				  o_crc_parallel_data <= A;	 
				  o_crc_en <= 'b1;
				  o_crc_last_byte <= 'b0;			
					
		
		if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin    
		    if (  (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= A['d7] ;
		   o_crc_data_valid <= 'b1;
		  
           end
          
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= A['d6 - counter] ;
			    if ( counter == 'd6 ) begin
			      o_ddrccc_mode_done <= 'b1;
			    end
			//	o_crc_data_valid <= 'b0;
				end
			    
			 end
			 
			else if ( (counter == 'd7) )
			  begin
			 reset_counter_flag <= 0;
			 
			 end
			 
			 
			 
		 end	
		 
		 /////////////////////////////////
		 
		 
		 calculating_Parity : begin
		   o_crc_en <= 'b0;
		   if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin
		      
		     if (  (!reset_counter_flag))
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
			  
			 end

		 end	  
		 
		 
		 /////////////////////////////////
				  				  		  
		token_CRC :	 begin

		/* if (crc_indicator)
				crc <= crc_temp;
		  else 	
				crc <= i_crc_crc_value;*/
				

		if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
    
		    if ( (!reset_counter_flag))
		     begin
          counter <= 'd0;
          reset_counter_flag <= 1;
          o_sdahnd_serial_data <= token[3];
		   o_crc_en <= 'b1;
		   o_crc_last_byte <= 'b1;
		  
			end
			  else
			    begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= token[(2 - counter)];
			    if ( counter == 'd2 )
					begin 
			      o_ddrccc_mode_done <= 'b1;
					
					end
			    end
			    
			 end
			 
			else if ( counter == 3 )
			  begin
			 reset_counter_flag <= 0;
			 
			 end

		 end	 
		
		/////////////////////////////////////////
		 
		/*CRC_value :  begin
		  crc_indicator <= 'b0;
		
		if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if ( (!reset_counter_flag))
		       begin
		        o_sdahnd_serial_data <= crc[4]; 
				counter <= 'd0;
				reset_counter_flag <= 1;  
           end
			   else
			     begin
			    counter <= counter + 1;
			    o_sdahnd_serial_data <= crc[(3 - counter)];
			    if ( counter == 'd3 )
			      o_ddrccc_mode_done <= 'b1;
			    end
			  end
			    
			else if ( counter == 'd4 )
			 begin
			  reset_counter_flag <= 0; 
			 end
			 
			 
				
			 
	  end*/
	  	 
		CRC_value :  begin
		  crc_indicator <= 'b0;
		  
		if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if ( (!reset_counter_flag))
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
			 end
			 
			 
				
			 
	  end
			  
			  /////////////////////////////////////////////
		/*	  
		restart_Pattern: begin
			  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if (!reset_counter_flag)
		       begin
		        o_sdahnd_serial_data <= 1;
            counter <= 'd0;
            reset_counter_flag <= 1; 
           end
           
			   else
			    begin
			     counter <= counter + 1;
			     o_sdahnd_serial_data <= !o_sdahnd_serial_data;
			     if ( counter == 'd3 )                                //was 4 , modified by laila
			      o_ddrccc_mode_done <= 'b1;
			    end	  
			  end
			 
	    else if ( counter == 'd4 )
			 begin
			  reset_counter_flag <= 0;

			 end
		  end
		  */
		  restart_Pattern: begin
			  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if (!reset_counter_flag)
		       begin
		        o_sdahnd_serial_data <= 1;
            counter <= 'd0;
            reset_counter_flag <= 1; 
           end
           
			   else
			    begin
			     counter <= counter + 1;
			    //  12 / 6 / 2024
			    o_sdahnd_serial_data <= tmp_restart[(3 - counter)];
			     if ( counter == 'd3 )  //before : 4
			      o_ddrccc_mode_done <= 'b1;
			    end	  
			  end
			 
	    else if ( counter == 'd4 )   //before: 5
			 begin
			  reset_counter_flag <= 0;
			 end
		  end
			  ////////////////////////////////////////////
			  
		exit_Pattern: begin
			  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		    begin    
		     if (!reset_counter_flag)
		       begin
		        o_sdahnd_serial_data <= 1;
                counter <= 'd0;
                reset_counter_flag <= 1; 
               end
           
			 else
			    begin
			     counter <= counter + 1;
			     o_sdahnd_serial_data <= !o_sdahnd_serial_data;
			     if ( counter == 'd7 )  begin  
			     // o_ddrccc_mode_done <= 'b1;
			      o_sdahnd_serial_data <= 'b0;
			end
			    end	  
			  end
			 
	    else if ( counter == 'd8 ) begin //7
			  reset_counter_flag <= 0;
			  o_sdahnd_serial_data <= 'b0;

		end

		else if ( counter == 'd7 )  begin  
			      o_ddrccc_mode_done <= 'b1;
			      o_sdahnd_serial_data <= 'b0;
			end

		  end
		
		////////////////////////////////////////////////
		
		endcase
		end		
		
		else
		  begin
		 	o_sdahnd_serial_data<= 1;
			o_ddrccc_mode_done<= 0;
			o_crc_en<= 0;
		    counter <= 0;
		    reset_counter_flag <= 0;
		    end
		    
		end
		

	
	endmodule

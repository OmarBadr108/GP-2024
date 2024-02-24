module tx (
input        i_sys_clk,
input        i_sys_rst,
input        i_ddrccc_tx_en,
input        i_sclgen_scl_pos_edge,
input        i_sclgen_scl_neg_edge,
input [3:0]  i_ddrccc_tx_mode,
input [7:0]  i_regf_tx_parallel_data,
input [7:0]  i_ddrccc_address, // special from ddr or ccc   
input [4:0]  i_crc_crc_value,

output reg        o_sdahnd_serial_data,
output reg        o_ddrccc_mode_done,
output reg [7:0]  o_crc_parallel_data,
output reg        o_ddrccc_parity_data,
output reg        o_crc_en
);


// tx modes needed  
localparam [3:0]  Serializing_address = 'b1010,   //done           
                  special_preamble_tx = 'b001,  //done
                  one_preamble = 'b010,   // done
                  zero_preamble = 'b011,  // done
				          Serializing_byte = 'b100, //done
				          serializing_zeros = 'b1100 , //done
				          CCC_value = 'b1101 ,
				          Calculating_Parity = 'b101,
				          CRC_value = 'b110,  //done
                  token_CRC = 'b111, //done
                  Restart_Pattern = 'b1000,
                  Exit_Pattern = 'b1001;

/*****special values****/			  
reg [1:0] special_preamble = 'b01 ;
reg [3:0] token = 4'b1100;

/***internal signals****/
wire parity_adj;
wire [7:0] A ; //CMD_Word_Second_Byte
reg [7:0] D1, D2; //first_and_second_Data_Bytes

/***helpful flags****/
integer counter;
integer value;
integer N;
reg reset_counter_flag;
reg rd_wr_flag;
reg [1:0] par;
reg first_byte_full;


assign A = {i_ddrccc_address[6:0],parity_adj}; 
assign parity_adj = (!( rd_wr_flag ^ (^7'b0) ^ (^i_ddrccc_address) ) );


 always @ (posedge i_sys_clk or negedge i_sys_rst)
	begin 
	
		if(~i_sys_rst) begin 
		    o_sdahnd_serial_data<= 1;
        o_ddrccc_mode_done<= 0;
        o_crc_parallel_data<= 0;
        o_ddrccc_parity_data<= 0;
        o_crc_en<= 0;
		    counter <= 0;
		    reset_counter_flag <= 0;
		    value <= 0;
		end 
		
		else if (i_ddrccc_tx_en) begin
		  
		o_ddrccc_mode_done <= 0;
		
		case (i_ddrccc_tx_mode)
		  
		  ///////////////
		  
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
			    counter <= counter + 1;
			    
			 end
			 
			else if ( counter == 'd7 )
			  begin
			 o_ddrccc_mode_done <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 7;
			 end
		  
		  end
	
		/////////////////////////////////
		  
		one_preamble : begin
		  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		     
		     if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 0;
           reset_counter_flag <= 1;
           o_sdahnd_serial_data <= 1;
          end
			 end
			 
			else if ( counter == 'd0 )
			  begin
			 o_ddrccc_mode_done <= 'b1;
			 rd_wr_flag <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 0;
			 end
		  end
		  
		  ////////////////////////////
		  
		 zero_preamble : begin
		  
		  if (i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
		   begin
		     if ( (counter == value) & (!reset_counter_flag) )
		      begin
           counter <= 'd0;
           reset_counter_flag <= 1;
   		      o_sdahnd_serial_data <= 0;
          end
			 end
			 
			else if ( counter == 'd0 )
			  begin
			 o_ddrccc_mode_done <= 'b1;
			 rd_wr_flag <= 'b0;
			 reset_counter_flag <= 0;
			 value <= 0;
			 end
		  end
		  
		  /////////////////////////////////////
		
		special_preamble_tx : begin
		  
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
			    end
			    
			 end
			 
			else if ( counter == 'd1 )
			  begin
			 o_ddrccc_mode_done <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 1;
			 end
			 
		 end	
		 ////////////////////////////////////
		 
		
		 ///////////////////////////////////
		  
		Serializing_byte :  begin
		  
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
			    end
			 end
			 
	 else if ( counter == 'd7 )
			begin
			 o_ddrccc_mode_done <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 7;
			 if (!first_byte_full)
			   begin
			    D1 <= i_regf_tx_parallel_data;
			    first_byte_full <= 1;
			   end
			 else
			    D2 <= i_regf_tx_parallel_data;
		  end
			 
	 end	
	 
	 /////////////////////////////
		 
		Serializing_address :  begin

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
			    end
			    
			 end
			 
			else if ( (counter == 'd7) )
			  begin
			 o_ddrccc_mode_done <= 'b1;
			 reset_counter_flag <= 0;
			 value <= 7;
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
			    end
			    
			 end
			 
			else if ( counter == 3 )
			  begin
			 o_ddrccc_mode_done <= 'b1;
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
			    end
			  end
			    
			else if ( counter == 'd4 && !i_sclgen_scl_neg_edge )
			 begin
			  o_ddrccc_mode_done <= 'b1;
			  reset_counter_flag <= 0;
			  value <= 4;
			 end
			  
		  
		  end
		
		
		endcase
		end		
		
		else
		  begin
		 	  o_sdahnd_serial_data<= 1;
        o_ddrccc_mode_done<= 0;
        o_crc_parallel_data<= 0;
        o_ddrccc_parity_data<= 0;
        o_crc_en<= 0;
		    counter <= 0;
		    reset_counter_flag <= 0;
		    value <= 0;
		    end
		    
		end
		

	
	endmodule
	


module tx (
input        i_sys_clk,
input        i_sys_rst,
input        i_ddrccc_tx_en,
input        i_sclgen_scl_pos_edge,
input        i_sclgen_scl_neg_edge,
input [4:0]  i_bitcnt_bit_count,
input [3:0]  i_ddrccc_tx_mode,
input [15:0] i_regf_tx_parallel_data,
input [6:0]  i_ddrccc_address, // special from ddr or ccc   
input [4:0]  i_crc_crc_value
input        i_crc_crc_valid,
input        i_regf_wr_rd_bit,


output        o_sdahnd_serial_data,
output        o_ddrccc_mode_done,
output [15:0] o_crc_parallel_data,
output        o_ddrccc_parity_data,
output        o_crc_en
);


// tx modes needed  
localparam [3:0]  Serializing_command_word = 'b000,
                  Serializing_address = 'b1010,              
                  special_preamble_tx = 'b001,  //01
                  one_preamble = 'b010,   // send 1 in pp or od 
                  zero_preamble = 'b011,  // send zero
				          Serializing_byte = 'b100, 
				          Calculating_Parity ='b101,
				          CRC_value = 'b110,
                  token_CRC = 'b111,
                  Restart_Pattern = 'b1000,
                  Exit_Pattern = 'b1001;



/************specila values*//////////////				  
localparam seven_zeros = 7'b0;				  
				  


/****************************************/
reg parity_adj;
reg [1:0] special_preamble = 'b10 ; 
reg [1:0] par;
reg [7:0] command_word ;
reg [7:0] address ;
reg [3:0] token = 4'b1100;
reg [15:0] D = i_regf_tx_parallel_data;
reg [15:0] A = i_regf_tx_parallel_data;

 
 
 
 always @ (posedge i_sys_clk or negedge i_sys_rst)
	begin 
	
		if(~i_sys_rst) begin 
		    o_sdahnd_serial_data<= 1;
        o_ddrccc_mode_done<= 0;
        o_crc_parallel_data<= 0;
        o_ddrccc_parity_data<= 0;
        o_crc_en<= 0;
		
		end 
		
		else if (i_ddrccc_tx_en) begin
		  
		o_ddrccc_mode_done <= 0;
		
		
		case (i_ddrccc_tx_mode)
		
		special_preamble_tx :begin 
		  
			if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			  o_sdahnd_serial_data <= special_preamble['d1 - i_bitcnt_bit_count]; //////
			
			if (i_bitcnt_bit_count == 'd2 )
			  o_ddrccc_mode_done <= 'b1;

				end

		
		Serializing_command_word : begin  ////////3ayez adomo ya mo5 m3 el address
			
			command_word <= {i_regf_wr_rd_bit,seven_zeros};  //
            if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			o_sdahnd_serial_data <= command_word[i_bitcnt_bit_count-'d3];
			else 
			o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd10 )
			o_ddrccc_mode_done <= 'b1;
			else
            o_ddrccc_mode_done <= 'b0;
			
			end
		
				 

		Serializing_address : begin 
		   parity_adj <=  (1 ^ (i_ddrccc_address[1]^i_ddrccc_address[3]^i_ddrccc_address[5]^i_regf_wr_rd_bit) );
       address <= {i_ddrccc_address,parity_adj};
       
      if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			  o_sdahnd_serial_data <= command_word[i_bitcnt_bit_count-'d11];
			else 
			  o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd18 )
			  o_ddrccc_mode_done <= 'b1;
			else
        o_ddrccc_mode_done <= 'b0;
			
			  o_ddrccc_parity_data <= 0;
			

			end
			
			
			
		Calculating_Parity : begin 
		  
		  if (i_bitcnt_bit_count < 'd6)
		    begin
		      par[0] <= (address[0]^address[2]^address[4]^address[6]);
		      par[1] <= (address[1]^address[3]^address[5]^address[7]); // must be equal one 
		      o_ddrccc_parity_data <= 0;
		    end
		    
		  else
		    begin
		     par[0] <= (D[15] ^ D[13] ^ D[11] ^ D[9] ^ D[7] ^ D[5] ^ D[3] ^ D[1]);
		     par[1] <= (D[14] ^ D[12] ^ D[10] ^ D[8] ^ D[6] ^ D[4] ^ D[2] ^ D[0] ^ 1'b1); 
		     o_ddrccc_parity_data <= 1;
		    end
		    
		    
		  if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
		     o_sdahnd_serial_data <= par['d19 - i_bitcnt_bit_count];
			
			if (i_bitcnt_bit_count == 'd19 )
			   o_ddrccc_mode_done <= 'b1;
			
			end
			

		
		one_preamble : begin 
		     
			o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd1 or i_bitcnt_bit_count == 'd2 )
			   o_ddrccc_mode_done <= 'b1;
			
			end
		
		
				
		zero_preamble : begin 
		   
		  if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			  o_sdahnd_serial_data <= 'b0;		
			
			if (i_bitcnt_bit_count == 'd1 or i_bitcnt_bit_count == 'd2 )
			  o_ddrccc_mode_done <= 'b1;
			
			end
			
				  
				  
		Serializing_byte : begin

		    to_be_serialized <= i_regf_tx_parallel_data ;
		    o_crc_en <= 1;
		    o_crc_parallel_data <= i_regf_tx_parallel_data; //3ayez anasak m3 fatma 
		      
		    if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
		       o_sdahnd_serial_data <= to_be_serialized[ 'd17 - i_bitcnt_bit_count];
		       
		    if (i_bitcnt_bit_count == 'd17 )
			     o_ddrccc_mode_done <= 'b1;

		    end
                  

				  				  		  
		token_CRC :	 begin
		  
		  if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
		    o_sdahnd_serial_data <= token['d3 - i_bitcnt_bit_count] ;
		    
		  if (i_bitcnt_bit_count == 'd4 )
			  o_ddrccc_mode_done <= 'b1;
		
		 end	 
		
		
		
		 
		CRC_value :  begin
		  
		  if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
		    o_sdahnd_serial_data <= i_crc_crc_value['d3 - i_bitcnt_bit_count] ;
		    
		  if (i_bitcnt_bit_count == 'd9 )
			  o_ddrccc_mode_done <= 'b1;
		  
		  end
           
            
                 
		
		Restart_Pattern:  
		
		
		Exit_Pattern:
		
		
		
		endcase
		end
	
	
	
	
	
	
	endmodule

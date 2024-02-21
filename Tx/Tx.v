module tx (
input  i_sys_clk,
input  i_sys_rst,
//input  i_sclgen_scl,
input  i_ddrccc_tx_en
input  i_sclgen_scl_pos_edge,
input  i_sclgen_scl_neg_edge,
input [4:0] i_bitcnt_bit_count,
input [] i_ddrccc_tx_mode,
input [7:0] i_regf_tx_parallel_data,
input [6:0] i_ddrccc_address, // special from ddr or ccc   
input [4:0] i_crc_crc_value
input  i_crc_crc_valid,
input  i_regf_wr_rd_bit,


output o_sdahnd_serial_data,
output o_ddrccc_mode_done,
output [7:0] o_crc_parallel_data,
output o_ddrccc_parity_data,
output o_crc_en
);


// tx modes needed  
localparam [3:0]  Serializing_command_word = 'b000,
                  Serializing_address = 'b1010,              
                  special_preamble_tx = 'b001,  //01
                  one_preamble = 'b010,   // send 1 in pp or od 
                  zero_preamble = 'b011,  // send zero
				  Serializing_byte = 'b100, 
                  Calculating_Parity_command ='b101,
				  Calculating_Parity_Data ='b101,
				  CRC_value = 'b0111,
                  token_CRC = 'b111,
                  Restart_Pattern = 'b1000,
                  Exit_Pattern = 'b1001;



/************specila values*//////////////				  
localparam seven_zeros = 7'b0;				  
				  


/****************************************/
reg parity_adj;
reg [1:0] special_preamble = 'b10 , par;
reg [7:0] command_word ;
reg [7:0] address ;

 
 
 
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
			o_sdahnd_serial_data <= special_preamble[i_bitcnt_bit_count-'d1];
			else 
			o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd2 )
			o_ddrccc_mode_done <= 'b1;
			else
            o_ddrccc_mode_done <= 'b0;	


				end
		
							
							
		
		
		Serializing_command_word : begin
			
			command_word <= {seven_zeros,i_regf_wr_rd_bit};
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
		parity_adj <=  (1 ^ (i_ddrccc_address[1]^i_ddrccc_address[3]^i_ddrccc_address[5]^
						  i_regf_wr_rd_bit) );

			address <= {parity_adj,i_ddrccc_address};
            if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			o_sdahnd_serial_data <= command_word[i_bitcnt_bit_count-'d11];
			else 
			o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd18 )
			o_ddrccc_mode_done <= 'b1;
			else
            o_ddrccc_mode_done <= 'b0;
			
			end
			
			
			
		Calculating_Parity_command : begin 
		par[0] <= (address[0]^address[2]^address[4]^address[6]);
		par[1] <= (address[1]^address[3]^address[5]^address[7]); // must be equal one
		   if (i_sclgen_scl_neg_edge or i_sclgen_scl_pos_edge)
			o_sdahnd_serial_data <= par[i_bitcnt_bit_count-'d19];
			else 
			o_sdahnd_serial_data <= 'b1;
			
			if (i_bitcnt_bit_count == 'd20 )
			o_ddrccc_mode_done <= 'b1;
			else
            o_ddrccc_mode_done <= 'b0;
			
			end
 
		
		
		one_preamble 
		
		
		zero_preamble
				  
				  
		Serializing_byte 
                  
				  
		Calculating_Parity_Data :
				  				  
				  
		CRC_value 
                 

		token_CRC 
                 
		
		Restart_Pattern
		
		
		Exit_Pattern 
		
		
		
		
	
	
	
	
	
	
	endmodule
	
	
 

 

module crc (
    input 		wire 		i_sys_clk,
    input 		wire 		i_sys_rst,
    input 		wire 		i_txrx_en,
	input       wire        i_txrx_data_valid,
	input 		wire 		i_txrx_last_byte,
    input 		wire [7:0]  i_txrx_data,
    output 		reg  [4:0]  o_txrx_crc_value,
    output 		reg 		o_txrx_crc_valid
);


parameter POLY = 6'b100101;
parameter POLY_WIDTH = 6;
parameter seed = 6'b011111;



reg [POLY_WIDTH-2:0] shift_reg ;
reg [3:0] counter;
reg feedback;
reg [7:0] temp;
 


// Initializations
always @(posedge i_sys_clk or negedge i_sys_rst) begin
    if (!i_sys_rst) begin
        
        shift_reg <= seed;
        counter   <= 'd0;
        o_txrx_crc_valid <= 'd0;
		o_txrx_crc_value <= 'd0;
		end 
	
	else	begin
		 if (i_txrx_en)
			begin
			if (i_txrx_last_byte)
				begin
					counter <= 'd0;
					o_txrx_crc_valid <= 'd1;
					o_txrx_crc_value <= shift_reg [4:0];
					shift_reg <= seed;
					
				end
			else if (i_txrx_data_valid)
				begin
					temp <= i_txrx_data;
					o_txrx_crc_valid <= 'd0;
					counter <= 'd0;
				end
				
			else 
				begin 
				if (counter == 'd8)
					begin
					//	counter <= 'd0;
						o_txrx_crc_valid <= 'd0;
					end
				else 
					begin 
						shift_reg[4] <= shift_reg[3]  ;     
						shift_reg[3] <= shift_reg[2] 			; 
						shift_reg[2] <= shift_reg[1] ^ feedback ;
						shift_reg[1] <= shift_reg[0] ;
						shift_reg[0] <= feedback ;
						counter <= counter + 'd1;
						o_txrx_crc_valid <= 'd0;
					end
					
				
				end
				
			end
			
			
		/*else
				begin
						counter <= 'd0;
						o_txrx_crc_valid <= 'd0;
						shift_reg <= POLY;
				end*/
				
				
				
		
		end
		
	end
	
	
	




always @(*) begin
 
	 case (counter) 
	'd0:	feedback = temp[7] ^ shift_reg[4] ;
	'd1:	feedback = temp[6] ^ shift_reg[4] ;
	'd2:	feedback = temp[5] ^ shift_reg[4] ;
	'd3:	feedback = temp[4] ^ shift_reg[4] ;
	'd4:	feedback = temp[3] ^ shift_reg[4] ;
	'd5:	feedback = temp[2] ^ shift_reg[4] ;
	'd6:	feedback = temp[1] ^ shift_reg[4] ;
	'd7:	feedback = temp[0] ^ shift_reg[4] ;
	
	default : feedback = 'b0;
	
	endcase
	
	end






endmodule
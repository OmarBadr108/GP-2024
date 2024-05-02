module CRC_TB ();
	reg i_sys_clk_tb, 
	  	i_sys_rst_tb, 
		i_input_valid_tb,
		i_enable_tb,
		i_end_byte_tb;
	reg [7:0] i_parallel_data_tb;  // Asynchronous reset active low
	wire [4:0] o_crc_value_tb;
	wire o_crc_valid_tb;

parameter clk_period=10;

always #(clk_period/2) i_sys_clk_tb=~i_sys_clk_tb;
//DUT
crc_variable_input DUT(
.i_sys_clk(i_sys_clk_tb),
.i_sys_rst(i_sys_rst_tb),
.i_parallel_data(i_parallel_data_tb),
.i_input_valid(i_input_valid_tb),
.i_enable(i_enable_tb),
.i_end_byte(i_end_byte_tb),
.o_crc_value(o_crc_value_tb),
.o_crc_valid(o_crc_valid_tb));


//initial block
initial
begin
  i_sys_clk_tb = 1'b1;
i_input_valid_tb = 1'b0;
i_end_byte_tb = 1'b0;
i_sys_rst_tb = 1'b0;
#(3*clk_period);
i_sys_rst_tb = 1'b1;
i_enable_tb = 1'b1;
i_parallel_data_tb = 8'hCB;
i_input_valid_tb = 1'b1;
#(clk_period);
i_input_valid_tb = 1'b0;
#(7*clk_period);
i_end_byte_tb = 1'b1;
#(15*clk_period);
$stop;
end
endmodule 

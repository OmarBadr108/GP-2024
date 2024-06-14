module mux #(parameter WIDTH = 8) (
	input wire  [WIDTH-1:0] i_mux_one , i_mux_zero ,
	input wire	 	 	    i_selector ,
	output reg  [WIDTH-1:0] o_mux_out 

	);

	always @(*) begin
		if(i_selector) begin
			o_mux_out = i_mux_one ;
		end
		else begin  
			o_mux_out = i_mux_zero ;
		end
	end
endmodule 
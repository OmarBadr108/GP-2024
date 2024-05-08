module mux8 (
input [7:0] tx,rx,
input en,
output reg [7:0] y 
);


always @ (*) 
	begin 
		if (en)
			y = tx;
		else 
			y = rx ;
	end 
	
endmodule 
		

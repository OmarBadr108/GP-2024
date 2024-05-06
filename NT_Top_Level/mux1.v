module mux1 (
input tx,rx,en,
output reg y 
);


always @ (*) 
	begin 
		if (en)
			y = tx;
		else 
			y = rx ;
	end 
	
endmodule 
		

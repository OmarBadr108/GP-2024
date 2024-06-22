module reg_file_t #(parameter WIDTH = 8 , DEPTH = 2**10 , ADDR = 10 )

	( input  wire			     i_regf_clk  		  ,   // clock , connected to the 50mhz clock , input from controller
	  input  wire			     i_regf_rst_n	     ,  	// active low reset , input from controller
	  input  wire			     i_regf_rd_en 	  ,  	// read data enable , input from controller
	  input  wire			     i_regf_wr_en 	  ,  	// write data enable, pulse at the end of the last bit , input from controller
	  input  wire [ADDR-1:0]  i_regf_addr  	  ,  	// adress of the reg file , input from controller
	  input  wire [WIDTH-1:0] i_regf_data_wr	  ,	// data write  , input from rx
	 
	  output reg [15:0]      o_frmcnt_max_rd_len ,
	  output reg [15:0]      o_frmcnt_max_wr_len ,
	  output reg  [WIDTH-1:0] o_regf_data_rd    			   	// data read   ,  output to tx

	 );

 reg [WIDTH-1:0] reg_array [DEPTH-1:0] ;  // 32 entry * 8 bits
 integer i;
 
 parameter Start_From = 'd1000,
           max_rd_location = 'd100,
           max_wr_location = 'd150; //other for special storing
 
 always @(posedge i_regf_clk or negedge i_regf_rst_n)
 	begin: regf_file_always
 		if (!i_regf_rst_n)
 			begin
 				for (i=0 ; i<DEPTH ; i=i+1)
 				 reg_array[Start_From + i] = 8'b11111111 + i ; //any data just after reset
 				 
 				reg_array[max_rd_location] = 'd0;
 		                reg_array[max_rd_location + 1] = 'd4;
 		
 		                reg_array[max_wr_location] = 'd0;
 		                reg_array[max_wr_location + 1 ] = 'd2; 
 		    
 			end

 		else
 		  begin
 		  		o_frmcnt_max_rd_len <= {reg_array[max_rd_location],reg_array[max_rd_location + 1]};
 		  		o_frmcnt_max_wr_len <= {reg_array[max_wr_location],reg_array[max_wr_location + 1]};
 		  					
 		    if (i_regf_rd_en && !i_regf_wr_en) 
 				 o_regf_data_rd <= reg_array [i_regf_addr];
 				 
 		    else if (i_regf_wr_en && !i_regf_rd_en) 
 			  	reg_array [i_regf_addr] <= i_regf_data_wr;
 	    end
 	    
 	 end

endmodule


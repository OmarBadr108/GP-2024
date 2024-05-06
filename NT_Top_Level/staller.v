module scl_staller(
input wire       i_stall_clk ,
input wire       i_stall_rst_n,
input wire       i_stall_flag,
input wire [4:0] i_stall_cycles,
output reg       o_stall_done,
output reg       o_scl_stall
    );
    
 reg [4:0] count = 4'b0 ;
    
always@(posedge i_stall_clk or negedge i_stall_rst_n)
 begin 
  if(~i_stall_rst_n)
    begin 
      o_scl_stall <= 1'b0 ;
      count <= 5'b0 ;
	  o_stall_done <= 1'b0;
    end
  else if(i_stall_flag)
    begin
      if (i_stall_cycles == count)  
        begin
            o_scl_stall <= 1'b0 ;
            count <= 5'b0 ;
            o_stall_done <= 1'b1;
        end        
      else 
        begin      
            o_scl_stall <= 1'b1 ; 
            count <= count + 5'b1 ;
        end
    end
	
	else 
	begin
		o_stall_done <= 1'b0;
		o_scl_stall <= 1'b0 ;
	end
		
  end
    
endmodule

module Restart_Detector (

input	   i_sys_clk ,
input 	   i_sys_rst ,
input 	   i_scl ,
input      i_sda ,

output reg o_engine_done
); 

reg [1:0] count;
reg [2:0] state;
		
always @ (posedge i_sys_clk , negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
    count <= 0;
    state <= 0;
   end

  else
   begin

 case (state)
 
0:begin
     o_engine_done <= 0;
     if (i_sda && i_scl && count != 1)
      count <= count + 1;
     else if(i_sda && !i_scl && count == 1)
      begin
       state <= 1;
       count <= 0;
      end
     else
      state <= 0;
   end

1:begin
     if (count != 1)
      count <= count + 1;
     else if(!i_sda && !i_scl && count == 1)
      begin
       state <= 2;
       count <= 0;
      end
     else
      state <= 0;
   end

2:begin
     if (count != 1)
      count <= count + 1;
     else if(i_sda && !i_scl && count == 1)
      begin
       state <= 3;
       count <= 0;
      end
     else
      state <= 0;
   end

3:begin
     if (count != 1)
      count <= count + 1;
     else if(!i_sda && !i_scl && count == 1)
      begin
       state <= 4;
       count <= 0;
      end
     else
      state <= 0;
   end

4:begin
     if (count != 1)
      count <= count + 1;
     else if(i_sda && !i_scl && count == 1)
      begin
       state <= 5;
       count <= 0;
      end
     else
      state <= 0;
   end 
 
5:begin
     if (i_sda && i_scl && count != 1)
      count <= count + 1;
     else if(count == 1)
      begin
       o_engine_done <= 1;
       count <= 0;
       state <= 0;
      end
     else
      state <= 0;
   end
endcase
end
end
 endmodule

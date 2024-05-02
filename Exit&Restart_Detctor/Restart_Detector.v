module Restart_Detector (

input	   i_sys_clk ,
input 	   i_sys_rst ,
input	   i_cccnt_enable,
input 	   i_scl ,
input      i_sda ,

output reg o_cccnt_done
  
); 
reg    	   [1:0]         current_state , next_state ;
reg                      count_done , en_count;
reg        [3:0]         count;

localparam [1:0]    	idle = 'd0,
						sda_n_scl = 'd1,
						four_transitions ='d2 ,
						pos_scl  = 'd3;

always @(negedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
     current_state <= idle ;		
   end
  else
   begin
     current_state <= next_state ;
   end
 end
 
 
 
 
 
 always @ (*)
	begin
	
	case (current_state)
		 
			
			idle : begin 
						o_cccnt_done <= 'b0;	
						if(i_cccnt_enable)
							begin 
							next_state <= sda_n_scl ;
							end
						else 
							begin
							next_state <= idle ;
							
							end
			end
			
			
			sda_n_scl : begin 
						o_cccnt_done <= 'b0;
						if(i_sda && !i_scl)
							begin 
							next_state <= four_transitions ;
						//	en_count <= 'b1;
							end
						else 
							begin
							next_state <= sda_n_scl ;
							end
			end
			
			
			four_transitions : begin 
					o_cccnt_done <= 'b0;
					en_count <= 'b1;
					
					case(count)
					'd1 : 		begin 
							if (!i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
					'd2 : 		begin 
							if (!i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
					
					'd3 : 		begin 
							if (i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
							
					'd4 : 		begin 
							if (i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
							
					'd5 : 		begin 
							if (!i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
							
					'd6 : 		begin 
							if (!i_sda && !i_scl)
								next_state <= four_transitions;
							else 
								next_state <= sda_n_scl;
							end
							
							
					'd7 : 		begin 
							if (i_sda && !i_scl)
								next_state <= pos_scl;
							else 
								next_state <= sda_n_scl;
							end
							
					default : begin 
					
							next_state <= sda_n_scl;
							
							end
							
											
					
					
					endcase
			end
			
			
			pos_scl : begin 
							en_count <= 'b0;		 
							
							if (i_sda && i_scl)
								begin
								next_state <= idle;
								o_cccnt_done <= 'b1;
								end
								
							else 
								begin
								next_state <= pos_scl;
								o_cccnt_done <= 'b0;
								end
							
					
						
			        end
			
			
		endcase 
		
	end
			
			
			
			
			
			
			
			
			
always @(posedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
   begin
     count <= 'b0 ;
	// count_done <= 'b0;
  
   end
  
  else
   begin
   
	if (en_count)
	  begin 
		if (count == 'd13)
			begin
		//	count_done <= 'b1;
			count <= 'b0 ;
			end
		else 
			begin
				count <= count +'d1 ;
		///		count_done <= 'b0;
			end
	   end 
	   
	 else 
		begin 
			count <= 'b0 ;
		//	count_done <= 'b0;
		end 
			
   end
 end
 
 
 
 endmodule
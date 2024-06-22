
//Active high tristate buffer
module tri_state_buf (
	input  wire  i_tri_state_data ,
	input  wire  i_tri_state_en   ,
	output wire  o_tri_state       );

	assign o_tri_state = (i_tri_state_en)?i_tri_state_data:1'bz;
	
endmodule
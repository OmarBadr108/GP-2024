`default_nettype none

module push_pull_behav_model(
	input   wire   i_sda_push_pull   , // 1 push :: 0 pull
	input   wire   i_push_pull_en    ,
	inout   wire   sda               ,
	output  wire   o_sda_push_pull  );

	wire tri_state_pull_in ;
	wire tri_state_push_in ;

	assign o_sda_push_pull   = sda;
	assign tri_state_pull_in = (i_push_pull_en) ? (i_sda_push_pull)  : 0 ;
	assign tri_state_push_in = (i_push_pull_en) ? (!i_sda_push_pull) : 0 ;

	// tri state buffer
	tri_state_buf u_push_tri_state_buf(
	.i_tri_state_data	(1'b0)                    ,
	.i_tri_state_en		(tri_state_push_in)       ,
	.o_tri_state		(sda)                    );

	tri_state_buf u_pull_tri_state_buf(
	.i_tri_state_data	(1'bz)                    ,
	.i_tri_state_en		(tri_state_pull_in)       ,
	.o_tri_state		(sda)                    );

endmodule

`default_nettype wire	
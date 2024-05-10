`default_nettype none

module open_drain_behav_model(
	input   wire   i_behav_model   ,
	inout   wire   sda                ,
	output  wire   o_behav_od  );

	assign o_behav_od = sda ;

	tri_state_buf_n u_tri_state_buf_n(
	.i_tri_state_data (1'b0)               ,
	.i_tri_state_en   (i_behav_model)   ,
	.o_tri_state      (sda)       		  );

endmodule

`default_nettype wire	
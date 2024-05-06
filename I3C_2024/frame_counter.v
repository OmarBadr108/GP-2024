`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    22:08:32 12/12/2022 
// Design Name: 
// Module Name:    frame_counter 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`default_nettype none
module frame_counter(
    input  wire  [7:0] i_fcnt_no_frms ,
    input  wire  i_fcnt_clk           ,
    input  wire  i_fcnt_rst_n         ,
    input  wire  i_fcnt_en            ,
    output reg   o_fcnt_last_frame
    );
	
reg [3:0] count = 4'b0 ;
wire      count_done   ;

// for tx : assign count_done = (count == i_fcnt_no_frms - 1'b1)? 1'b1 : 1'b0 ; we need to create mux at integration
assign count_done = (count == i_fcnt_no_frms)? 1'b1 : 1'b0 ;
always@(posedge i_fcnt_en or negedge i_fcnt_rst_n)
begin 
  if(~i_fcnt_rst_n)
    begin 
      o_fcnt_last_frame <= 1'b0 ;
      count <= 4'b0 ;
    end
  else if(i_fcnt_en && ~count_done)
    begin
      o_fcnt_last_frame <= 1'b0 ;
      count <= count + 4'b1 ;
    end
  else 
    begin
      o_fcnt_last_frame <= 1'b1 ; 
    end
end  
    

endmodule
`default_nettype wire
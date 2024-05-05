`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Mixel inc.
// Engineer: Zyad Sobhy
// 
// Create Date: 04/13/2023 12:10:20 AM
// Design Name: 
// Module Name: mux
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module gen_mux
#(parameter BUS_WIDTH = 4,
  parameter SEL = 5 )
( input wire [(BUS_WIDTH * (2**SEL) )-1:0] data_in,
  input wire [SEL-1:0] ctrl_sel,
  output reg [BUS_WIDTH-1:0] data_out );

  always @ ( * )
  begin
    data_out = data_in[ctrl_sel*BUS_WIDTH +: BUS_WIDTH];
  end
endmodule
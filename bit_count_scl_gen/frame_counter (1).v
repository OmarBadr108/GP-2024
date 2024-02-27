//`timescale 1ns / 1ps
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
module frame_counter_old (
    input  wire  [7:0] i_fcnt_no_frms     ,
    input  wire        i_fcnt_clk         ,
    input  wire        i_fcnt_rst_n       ,
    input  wire        i_fcnt_en          ,
    input  wire        i_regf_CMD_ATTR    ,     // HDR 1 bit only selects bit [0] (1 for immediate and 0 for regular)
    input  wire [15:0] i_regf_DATA_LEN    ,     // HDR 
    input  wire [2:0]  i_regf_DTT         ,     // HDR
    input  wire [5:0]  i_cnt_bit_count    ,     // HDR
    output reg         o_fcnt_last_frame  ,     
    output reg         o_cccnt_last_frame       // HDR
    );
	
reg [15:0] count = 4'b0 ;
wire       count_done   ;
/*
// for tx : assign count_done = (count == i_fcnt_no_frms - 1'b1)? 1'b1 : 1'b0 ; we need to create mux at integration
assign count_done = (count == i_fcnt_no_frms)? 1'b1 : 1'b0 ;
always@(posedge i_fcnt_en or negedge i_fcnt_rst_n)
begin 
  if(~i_fcnt_rst_n)
    begin 
      o_fcnt_last_frame <= 1'b0 ;
      count <= 16'b0 ;
    end
  else if(i_fcnt_en && ~count_done)
    begin
      o_fcnt_last_frame <= 1'b0 ;
      count <= count + 16'b1 ;
    end
  else 
    begin
      o_fcnt_last_frame <= 1'b1 ; 
    end
end  
*/ 
always @(posedge i_fcnt_clk or negedge i_fcnt_rst_n) begin 
    if (!i_fcnt_rst_n) begin 
        count <= 'd0 ;
        o_cccnt_last_frame <= 1'b0 ;
    end 
    else begin  
        if(i_fcnt_en) begin           
            if(i_cnt_bit_count == 9 || i_cnt_bit_count == 19) begin 
                if (count == 'd0) begin 
                    o_cccnt_last_frame <= 1'b1 ;
                end 
                else begin
                    o_cccnt_last_frame <= 1'b0 ;
                    count <= count - 1 ;
                end
            end         
        end
     
      // reset counter 
        else begin
            o_cccnt_last_frame <= 1'b0 ;

            if(!i_regf_CMD_ATTR) begin      // regular
                count <= i_regf_DATA_LEN ; // DWORD1
            end 

        else begin                      // immediate 
          case (i_regf_DTT) 
          3'd0 : count <= 0 ;
          3'd1 : count <= 1 ;
          3'd2 : count <= 2 ;
          3'd3 : count <= 3 ;
          3'd4 : count <= 4 ;

          3'd5 : count <= 0 ;
          3'd6 : count <= 1 ;
          3'd7 : count <= 2 ;
          endcase
        end 
      end 
  end 
end

endmodule
//`default_nettype wire
module DualPortRegFile #(parameter WIDTH = 8 , ADDR = 15)
(
    input wire clk,                
    input wire reset,              
    input wire              wr_en,              // Write enable
    input wire              rd_en,              // Read enable
    input wire [ADDR-1  :0]  wr_addr,      // Write address
    input wire [WIDTH-1 :0] data_in,      // Data input for writing
    input wire [ADDR-1  :0]  rd_addr,      // Read address
    output reg [WIDTH-1 :0] data_out      // Data output for reading
);

reg [WIDTH-1:0] conf_regfile [(2**ADDR -1):0];          // 32kb registers, each 8 bits wide
integer i;

// Write operation
always @(posedge clk or negedge reset) begin
    if (!reset) begin
    
        for (i = 0; i < (2**ADDR); i = i + 1) begin
            conf_regfile[i] <= 8'b0;
        end
    end 
    else if (wr_en) begin
        conf_regfile[wr_addr] <= data_in;
    end 
end

always @(posedge clk) begin
    if (rd_en) begin 
        data_out <= conf_regfile[rd_addr];
    end 
end
endmodule
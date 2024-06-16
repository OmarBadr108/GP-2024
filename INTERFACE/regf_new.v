module DualPortRegFile (
    input wire clk,                // Clock input
    input wire reset,              // Synchronous reset input, active high
    input wire wr_en,              // Write enable
    input wire rd_en,
    input wire [3:0] wr_addr,      // Write address
    input wire [7:0] data_in,      // Data input for writing
    input wire [3:0] rd_addr,      // Read address
    output reg [7:0] data_out      // Data output for reading
);

reg [7:0] conf_regfile [15:0];          // 16 registers, each 8 bits wide

// Write operation
always @(posedge clk or negedge reset) begin
    if (!reset) begin
        integer i;
        for (i = 0; i < 16; i = i + 1) begin
            conf_regfile[i] <= 8'b0;
        end
    end 
    else begin 
    if (wr_en) begin
        conf_regfile[wr_addr] <= data_in;
    end
    else if (rd_en) begin 
        data_out = conf_regfile[rd_addr]
    end 
end

endmodule
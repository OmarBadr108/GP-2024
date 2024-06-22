module tb_DualPortRegFile;

  // Testbench signals
  reg clk;
  reg reset;
  reg wr_en;
  reg rd_en ;
  reg [14:0] wr_addr;
  reg [7:0] data_in;
  reg [14:0] rd_addr;
  wire [7:0] data_out;

  // Instantiate the DUT (Device Under Test)
  DualPortRegFile dut (
    .clk(clk),
    .reset(reset),
    .wr_en(wr_en),
    .rd_en   (rd_en),
    .wr_addr(wr_addr),
    .data_in(data_in),
    .rd_addr(rd_addr),
    .data_out(data_out)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz clock
  end

  // Test sequence
  initial begin
    // Initialize inputs
    reset = 1;
    wr_en = 0;
    wr_addr = 0;
    data_in = 0;
    rd_addr = 0;

    // Apply reset
    #10;
    reset = 0;
    #10;
    reset = 1;

    // Write and Read operations
    // Test Case 1: Write data to address 0 and read it back
    #10;
    wr_en = 1;
    wr_addr = 15'd0;
    data_in = 8'hAA;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    rd_addr = 15'd0;
    #10;
    $display("Read data at address 0: %h (expected: AA)", data_out);

    // Test Case 2: Write data to address 1 and read it back
    #10;
    wr_en = 1;
    wr_addr = 15'd1;
    data_in = 8'hBB;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    rd_addr = 15'd1;
    #10;
    $display("Read data at address 1: %h (expected: BB)", data_out);

    // Test Case 3: Write data to address 32766 and read it back
    #10;
    wr_en = 1;
    wr_addr = 15'd32767;
    data_in = 8'hCC;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    rd_addr = 15'd32767;
    #10;
    $display("Read data at address 32767: %h (expected: CC)", data_out);

    // Finish simulation
    #20;
    $stop;
  end

  // Monitor for debug purposes
  initial begin
    $monitor("Time: %0t, Reset: %b, wr_en: %b, wr_addr: %h, data_in: %h, rd_addr: %h, data_out: %h", 
             $time, reset, wr_en, wr_addr, data_in, rd_addr, data_out);
  end

endmodule
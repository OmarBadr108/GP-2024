module tb_Internal_Regfile;

  // Testbench signals
  reg clk;
  reg reset;
  reg wr_en;
  reg rd_en ;
  reg [4:0] addr;
  reg [7:0] data_in;

  wire [15:0] o_frmcnt_data_len ; 
  wire [2:0] o_cccnt_CMD_ATTR ;  
  wire [3:0] o_engine_TID ;      
  wire [7:0] o_ccc_CMD ;         
  wire [4:0] o_cccnt_DEV_INDEX ; 
  wire [2:0] o_frmcnt_DTT ;      
  wire [2:0] o_engine_MODE ;     
  wire      o_cccnt_RnW ;       
  wire      o_cccnt_WROC ;      
  wire      o_cccnt_TOC ;       
  wire      o_engine_CP ;       
  wire      o_cccnt_DBP ;       
  wire      o_cccnt_SRE ; 

  wire [7:0] data_out;
  reg  i_engine_Dummy_conf ;  

  // Instantiate the DUT (Device Under Test)
  Internal_Regfile dut (
    .*
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
    addr = 0;
    data_in = 0;
    rd_en = 0 ;
    // Apply reset
    #10;
    reset = 0;
    #10;
    reset = 1;
/*
    // Write and Read operations
    // Test Case 1: Write data to address 0 and read it back
    #10;
    wr_en = 1;
    addr = 5'd0;
    data_in = 8'hAA;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    addr = 15'd0;
    #10;
    $display("Read data at address 0: %h (expected: AA)", data_out);

    // Test Case 2: Write data to address 1 and read it back
    #10;
    rd_en = 0 ;
    wr_en = 1;
    addr = 5'd1;
    data_in = 8'hBB;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    addr = 5'd1;
    #10;
    $display("Read data at address 1: %h (expected: BB)", data_out);

    // Test Case 3: Write data to address 32766 and read it back
    #10;
    rd_en = 0 ;
    wr_en = 1;
    addr = 5'd31;
    data_in = 8'hCC;
    #10;
    wr_en = 0;
    rd_en = 1 ;
    addr = 5'd31;
    #10;
    $display("Read data at address 31: %h (expected: CC)", data_out);
*/
    // Finish simulation
    #20;

    i_engine_Dummy_conf = 1'b0 ;
    #10;
    wr_en = 1;
    rd_en = 0 ;
    addr = 5'd1;
    data_in = 8'hA0;
    #10;
    addr = 5'd2;
    data_in = 8'hB1;
    #10;
    addr = 5'd3;
    data_in = 8'h01;
    #10;
    addr = 5'd4;
    data_in = 8'h15;
    #10;
    addr = 5'd5;
    data_in = 8'h7b;
    #10;
    addr = 5'd6;
    data_in = 8'ha0;
    #10;
    addr = 5'd7;
    data_in = 8'hc0;
    #10;
    addr = 5'd8;
    data_in = 8'hac;
    #10;
    i_engine_Dummy_conf = 1'b1 ;
    #50;
    $stop;
  end

  // Monitor for debug purposes
  initial begin
    $monitor("Time: %0t, Reset: %b, wr_en: %b, wr_addr: %h, data_in: %h, data_out: %h", 
             $time, reset, wr_en, addr, data_in, data_out);
  end

endmodule
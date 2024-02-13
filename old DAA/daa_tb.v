`timescale 1us / 1ps

`default_nettype none
module daa_tb();

    // Clock and reset signals
    reg          i_sdr_clk_tb           ;
    reg          i_sdr_rst_n_tb         ;  
    reg          i_controller_en_tb     ;

   
    // Design Inputs           
    reg            i_i3c_i2c_sel_tb ;
    wire           sda_tb               ;    //bidirectional           
   
    // Design Output
    wire          o_sdr_rx_valid_tb     ;
    wire          o_ctrl_done_tb    ;
    wire          scl_tb                ;
 

    reg           sda_drive             ;  // locally driven value

    assign sda_tb   = sda_drive ;

    
    parameter SEQUENCE = 64'b0 ;
    parameter SEQUENCE2 = 'hFFFFFFFFFFFFFFFF  ;
    
    reg [63:0] randomized_seq;
    
    integer i ;
   
    // DUT instantiation
    i3c_controller_top i3c_top_dut (  
                       .i_sdr_clk          (i_sdr_clk_tb)        ,
                       .i_sdr_rst_n        (i_sdr_rst_n_tb)      ,
                       .i_i3c_i2c_sel      (i_i3c_i2c_sel_tb)    ,
                       .i_controller_en    (i_controller_en_tb)  ,
                       .scl                (scl_tb)              ,
                       .sda                (sda_tb)              ,
                       .o_sdr_rx_valid     (o_sdr_rx_valid_tb)   ,
                       .o_ctrl_done        (o_ctrl_done_tb)      );


initial 
    begin
        sda_drive =1'bz;
        i_sdr_clk_tb = 1'b0;
        i_i3c_i2c_sel_tb= 1'b1;

    
    // Generate the reset
        i_sdr_rst_n_tb = 1'b1;
        #20
        i_sdr_rst_n_tb = 1'b0;
        #20
        i_sdr_rst_n_tb = 1'b1;
     // INPUTS 
        i_controller_en_tb <= 1'b1 ; 
     // first testcase (testing sending 7E/W)
     //PASSED
    
     //2nd testcase (testing broadcast write nack)    
     
     //3rd testcase
     //Acknowledge after broadcast write
        #80100
        sda_drive = 1'b0;
        #10000
        sda_drive = 1'bz;
     //testcase passed with sending ENTDAA CCC correctly 
     //PARITY of ENTDAA passed successfully   
     //REPEATED START passed successfully
     //BROADCAST READ PASSED successfully 
     //sending ack after broadcast read
        #174960 
        sda_drive = 1'b0;
        #10000
     //READ DATA STATE, Arbitration happens and each target should send 48ID, BCR, DCR
   for (i=1 ; i<65 ; i=i+1) //8 Frames 
       begin
           @(negedge scl_tb)
              #10 sda_drive = SEQUENCE[i-1] ;    
        end 
        sda_drive = 1'bz;
   // 64 bits recieved from target correctly, written into reg file correctly 
   // assigned address writen into reg file correctily, serialized on the bus correctly
   // parity of assigned address serialized correctly
   // checkpoint: target ack after assigned address
   
        #80000
        sda_drive = 1'b0;
        #10000  
        sda_drive = 1'bz;
        
   // ACKNOLEDGE AFTER SECOND BROADCAST READ 
   
       #85300
       sda_drive = 1'b0;
       @(negedge scl_tb);

       
   // second target
     //READ DATA STATE, Arbitration happens and each target should send 48ID, BCR, DCR
   for (i=1 ; i<65 ; i=i+1) //8 Frames 
       begin
           @(negedge scl_tb)
              #10 sda_drive = $random%2 ;
              randomized_seq[64-i] = sda_drive;   
        end 
        sda_drive = 1'bz;
        
       #80000 
       sda_drive = 1'b0;
       #10000
       sda_drive = 1'bz;
       
       // ACK AFTER BROADCAST READ
        #85300
       sda_drive = 1'b0;
       @(negedge scl_tb);

       
   // second target
     //READ DATA STATE, Arbitration happens and each target should send 48ID, BCR, DCR
   for (i=1 ; i<65 ; i=i+1) //8 Frames 
       begin
           @(negedge scl_tb)
              #10 sda_drive = SEQUENCE2[i-1] ;  
        end 
        sda_drive = 1'bz;   
        
       // ACK AFTER BROADCAST READ
        #85300
        #85300
       sda_drive = 1'b0;
       @(negedge scl_tb);

          
   // second target
     //READ DATA STATE, Arbitration happens and each target should send 48ID, BCR, DCR
   for (i=1 ; i<65 ; i=i+1) //8 Frames 
       begin
           @(negedge scl_tb)
              #10 sda_drive = SEQUENCE2[i-1] ;  
        end 
        sda_drive = 1'bz;       
    
        #90000
        sda_drive = 1'b1;
        #10000
        sda_drive = 1'bz;     
    end
        

    // wait for Done flag to turn off I3C
     always @(posedge o_ctrl_done_tb) 
     begin 
        i_controller_en_tb <= 1'b0;
    end

   pullup(sda_tb);
// generate the clock 
   always #20 i_sdr_clk_tb = ~i_sdr_clk_tb;
      
endmodule
`default_nettype wire 
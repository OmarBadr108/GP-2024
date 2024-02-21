`timescale 1us / 1ps
`default_nettype none
module ENTHDR_tb();

    // Clock and reset signals
    reg          i_clk_tb           ;
    reg          i_rst_n_tb         ;  
    reg          i_controller_en_tb     ;

   
    // Design Inputs           
    reg          i_i3c_i2c_sel_tb ;
    reg          i_hdr_en_tb;
    wire         sda_tb                 ;

   
    // Design Output
    wire         o_sdr_rx_valid_tb     ;
    wire         o_ctrl_done_tb        ;
    wire         scl_tb                ;



 i3c_controller_top i3c_top_dut (  
                    .i_sdr_clk          (i_clk_tb)        ,
                    .i_sdr_rst_n        (i_rst_n_tb)      ,
                    .i_i3c_i2c_sel      (i_i3c_i2c_sel_tb)    ,
                    .i_controller_en    (i_controller_en_tb)  ,
                    .scl                (scl_tb)              ,
                    .sda                (sda_tb)              ,
                    .i_hdr_en           (i_hdr_en_tb)         ,
                    .o_sdr_rx_valid     (o_sdr_rx_valid_tb)   ,
                    .o_ctrl_done        (o_ctrl_done_tb)       );
 

 always #20 i_clk_tb = ~i_clk_tb;
 

    reg               sda_drive             ;  // locally driven value

    assign sda_tb   = sda_drive ;

 initial 
 begin
        i_clk_tb=0; 
        sda_drive =1'bz;
        i_i3c_i2c_sel_tb= 1'b1;
       

    
    // Generate the reset
        i_rst_n_tb = 1'b1;
        #20
        i_rst_n_tb = 1'b0;
        #20
        i_rst_n_tb = 1'b1;
     
     // INPUTS 
        i_controller_en_tb = 1'b1 ;
        i_i3c_i2c_sel_tb   = 1'b1;
        i_hdr_en_tb        = 1'b1;



   #80100

   $stop ;

 end 










endmodule
`default_nettype wire 

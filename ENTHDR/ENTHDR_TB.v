`timescale 1us / 1ps

`default_nettype none
module ENTHDR_tb();

    // Clock and reset signals
    reg          i_clk_tb           ;
    reg          i_rst_n_tb         ;  
    reg          i_controller_en_tb     ;

   
    // Design Inputs           
    reg          i_i3c_i2c_sel_tb ;
    wire         sda_tb                 ;            
   
    // Design Output
    wire         o_sdr_rx_valid_tb     ;
    wire         o_ctrl_done_tb        ;
    wire         scl_tb                ; 
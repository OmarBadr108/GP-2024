module RX_Target (

input                     i_sys_clk,
input                     i_sys_rst,
input                     i_sclgen_scl,
input                     i_sclgen_scl_pos_edge,
input                     i_sclgen_scl_neg_edge,
input                     i_ddrccc_rx_en,
input                     i_sdahnd_rx_sda,
//input     [4:0]           i_bitcnt_rx_bit_count,
input        [3:0]        i_ddrccc_rx_mode,
input                     i_crc_value,
input                     i_crc_valid,

output  reg  [7:0]        o_regfcrc_rx_data_out,
output  reg               o_ddrccc_rx_mode_done,
output  reg               o_ddrccc_pre,
output  reg               o_ddrccc_error,
output  reg               o_crc_en,                 
output  reg               o_crc_data_valid,
output  reg               o_ddrccc_error_done
);
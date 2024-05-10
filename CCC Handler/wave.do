onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /CCC_Handler_tb/RAND_TOC
add wave -noupdate /CCC_Handler_tb/RAND_RnW
add wave -noupdate /CCC_Handler_tb/RAND_DTT
add wave -noupdate /CCC_Handler_tb/RAND_CP
add wave -noupdate /CCC_Handler_tb/RAND_CMD_ATTR
add wave -noupdate /CCC_Handler_tb/RAND_CMD
add wave -noupdate /CCC_Handler_tb/o_txrx_addr_ccc_tb
add wave -noupdate /CCC_Handler_tb/o_sdahnd_serial_data_tb
add wave -noupdate /CCC_Handler_tb/o_sclstall_en_tb
add wave -noupdate /CCC_Handler_tb/o_scl_stall_tb
add wave -noupdate /CCC_Handler_tb/o_regf_wr_en_tb
add wave -noupdate /CCC_Handler_tb/o_regf_rd_en_tb
add wave -noupdate /CCC_Handler_tb/o_regf_addr_tb
add wave -noupdate /CCC_Handler_tb/o_frmcnt_en_tb
add wave -noupdate /CCC_Handler_tb/o_frmcnt_Direct_Broadcast_n_tb
add wave -noupdate /CCC_Handler_tb/o_fcnt_last_frame_tb
add wave -noupdate /CCC_Handler_tb/o_engine_done_tb
add wave -noupdate /CCC_Handler_tb/o_crc_parallel_data_tx_tb
add wave -noupdate /CCC_Handler_tb/o_crc_last_byte_tx_tb
add wave -noupdate /CCC_Handler_tb/o_crc_last_byte_rx_tb
add wave -noupdate /CCC_Handler_tb/o_crc_en_tb
add wave -noupdate /CCC_Handler_tb/o_bitcnt_err_rst_tb
add wave -noupdate /CCC_Handler_tb/mux8_out
add wave -noupdate /CCC_Handler_tb/mux1_out3
add wave -noupdate /CCC_Handler_tb/mux1_out2
add wave -noupdate /CCC_Handler_tb/mux1_out1
add wave -noupdate /CCC_Handler_tb/i_sys_clk_tb
add wave -noupdate /CCC_Handler_tb/i_stall_cycles
add wave -noupdate /CCC_Handler_tb/i_sdahnd_rx_sda_tb
add wave -noupdate /CCC_Handler_tb/i_sclstall_stall_done_tb
add wave -noupdate /CCC_Handler_tb/i_rx_regfcrc_data_wr_tb
add wave -noupdate /CCC_Handler_tb/i_regf_tx_parallel_data_tb
add wave -noupdate /CCC_Handler_tb/i_regf_TOC_tb
add wave -noupdate /CCC_Handler_tb/i_regf_RnW_tb
add wave -noupdate /CCC_Handler_tb/i_regf_DTT_tb
add wave -noupdate /CCC_Handler_tb/i_regf_DBP_tb
add wave -noupdate /CCC_Handler_tb/i_regf_DATA_LEN_tb
add wave -noupdate /CCC_Handler_tb/i_regf_CMD_tb
add wave -noupdate /CCC_Handler_tb/i_regf_CMD_ATTR_tb
add wave -noupdate /CCC_Handler_tb/i_frmcnt_last_frame_tb
add wave -noupdate /CCC_Handler_tb/i_engine_en_tb
add wave -noupdate /CCC_Handler_tb/i_crc_value_tb
add wave -noupdate /CCC_Handler_tb/i_crc_valid_tb
add wave -noupdate /CCC_Handler_tb/i_bitcnt_en_tb
add wave -noupdate /CCC_Handler_tb/en_mux
add wave -noupdate /CCC_Handler_tb/crc_en_tx
add wave -noupdate /CCC_Handler_tb/crc_en_rx
add wave -noupdate /CCC_Handler_tb/o_crc_data_valid_tx_tb
add wave -noupdate /CCC_Handler_tb/o_crc_data_valid_rx_tb
add wave -noupdate /CCC_Handler_tb/o_scl_tb
add wave -noupdate /CCC_Handler_tb/o_rx_mode_tb
add wave -noupdate /CCC_Handler_tb/o_rx_en_tb
add wave -noupdate /CCC_Handler_tb/i_rx_pre_tb
add wave -noupdate /CCC_Handler_tb/i_rx_mode_done_tb
add wave -noupdate /CCC_Handler_tb/i_rx_error_tb
add wave -noupdate /CCC_Handler_tb/i_tx_mode_done_tb
add wave -noupdate -radix unsigned /CCC_Handler_tb/o_tx_mode_tb
add wave -noupdate /CCC_Handler_tb/o_tx_en_tb
add wave -noupdate -color Gold -radix unsigned /CCC_Handler_tb/CCC_Handler_dut/next_state
add wave -noupdate -color Gold -radix unsigned /CCC_Handler_tb/CCC_Handler_dut/current_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {48205777 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 185
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {48205196 ns} {48206780 ns}

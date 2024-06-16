onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 24 -group TOP /I3C_TOP_TB/i_sdr_clk_tb
add wave -noupdate -height 24 -group TOP /I3C_TOP_TB/i_sdr_rst_n_tb
add wave -noupdate -height 24 -group TOP -color Magenta /I3C_TOP_TB/i_controller_en_tb
add wave -noupdate -height 24 -group TOP /I3C_TOP_TB/i_i3c_i2c_sel_tb
add wave -noupdate -height 24 -group TOP /I3C_TOP_TB/i_data_config_mux_sel_tb
add wave -noupdate -height 24 -group TOP /I3C_TOP_TB/frame_ended
add wave -noupdate /I3C_TOP_TB/sda_drive
add wave -noupdate -color Cyan /I3C_TOP_TB/scl_tb
add wave -noupdate /I3C_TOP_TB/sda_tb
add wave -noupdate /I3C_TOP_TB/DUT/u_enthdr/i_clk
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/START_BIT
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/SERIALIZING
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/PARITY
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/STOP
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/CTRL_ACK
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/Hold_Zero
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/CTRL_NACK
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/REPEATED_START
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_clk
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_rst_n
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_scl
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_scl_neg_edge
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_scl_pos_edge
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_en
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_valid
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_count
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_count_done
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_mode
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_ser_regf_data
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_timer_cas
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/i_timer_bus_free_pure
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_ser_sda_low
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_stop_pattern
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_start_pattern
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_ser_s_data
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_ser_mode_done
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_ser_pp_mode_done
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_tx_daa_done
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/o_ser_to_parity_transition
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/last_bit_flag
add wave -noupdate -height 24 -group SDR_TX /I3C_TOP_TB/DUT/u_controller_tx/parity_counter
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/i_sclgen_scl_pos_edge
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/i_sclgen_scl_neg_edge
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/i_ddrccc_tx_mode
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/i_regf_tx_parallel_data
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/o_sdahnd_serial_data
add wave -noupdate -height 24 -group HDR_TX -color Magenta /I3C_TOP_TB/DUT/tx/o_ddrccc_mode_done
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/counter
add wave -noupdate -height 24 -group HDR_TX -radix binary /I3C_TOP_TB/DUT/tx/i_ddrccc_special_data
add wave -noupdate -height 24 -group HDR_TX /I3C_TOP_TB/DUT/tx/parity_adj
add wave -noupdate /I3C_TOP_TB/DUT/u_enthdr/o_i3cengine_done
add wave -noupdate -color Magenta /I3C_TOP_TB/DUT/u_hdr_engine/i_i3cengine_hdrengine_en
add wave -noupdate /I3C_TOP_TB/DUT/tx/i_ddrccc_tx_en
add wave -noupdate /I3C_TOP_TB/DUT/u_hdr_engine/o_ccc_en
add wave -noupdate /I3C_TOP_TB/DUT/CCC_Handler/i_sclstall_stall_done_strtch
add wave -noupdate -height 30 -expand -group Staller /I3C_TOP_TB/DUT/u_scl_staller/o_stall_done
add wave -noupdate -height 30 -expand -group Staller /I3C_TOP_TB/DUT/u_scl_staller/o_scl_stall
add wave -noupdate -height 30 -expand -group Staller /I3C_TOP_TB/DUT/u_scl_staller/i_stall_flag
add wave -noupdate -height 30 -expand -group Staller -radix unsigned /I3C_TOP_TB/DUT/u_scl_staller/i_stall_cycles
add wave -noupdate -height 30 -expand -group Staller -radix unsigned /I3C_TOP_TB/DUT/u_scl_staller/count
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/IDLE
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/BROADCAST
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/ACK
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/ENTHDR_DDR
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/PARITY
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_rst_n
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_i3cengine_en
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_tx_mode_done
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_rx_ack_nack
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_scl_neg_edge
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_rx_mode_done
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/i_scl_pos_edge
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_pp_od
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_bit_cnt_en
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_regf_rd_en
add wave -noupdate -height 24 -group ENTHDR -radix decimal /I3C_TOP_TB/DUT/u_enthdr/o_regf_addr
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_tx_en
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_tx_mode
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_rx_en
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/o_rx_mode
add wave -noupdate -height 24 -group ENTHDR /I3C_TOP_TB/DUT/u_enthdr/state
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/i_scl_pos_edge
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/i_scl_neg_edge
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/o_enthdr_en
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/o_mode_sda_sel
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/o_hdrengine_en
add wave -noupdate -height 24 -group I3C_ENGINE -radix binary /I3C_TOP_TB/DUT/u_i3c_engine/state
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/hdr_en
add wave -noupdate -height 24 -group I3C_ENGINE /I3C_TOP_TB/DUT/u_i3c_engine/o_controller_done
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/i_TOC
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/i_CP
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/o_ddrmode_en
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/next_state
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/i_CP_temp
add wave -noupdate -height 24 -group HDR_ENGINE /I3C_TOP_TB/DUT/u_hdr_engine/i_TOC_temp
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_sys_clk
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_sys_rst
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_engine_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_frmcnt_last
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_tx_mode_done
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_rx_mode_done
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_rx_pre
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_rx_error
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_staller_done
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_toc
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_dev_index
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_short_read
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_wroc
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_wr_rd_bit
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_cmd_attr
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_regf_dtt
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/i_bitcnt
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_tx_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_tx_mode
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_rx_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_rx_mode
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_frmcnt_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_bitcnt_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_bitcnt_rst
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_sdahand_pp_od
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_regf_wr_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_regf_rd_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_regf_addr
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_sclstall_no_of_cycles
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_sclstall_en
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_engine_done
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_tx_special_data
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_regf_abort
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/o_regf_error_type
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/target_addres
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/broadcast_address
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/current_state
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/next_state
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/parity_data
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/Parity_data_seq
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/sysclk_done
add wave -noupdate -height 24 -group DDR /I3C_TOP_TB/DUT/DDR_NT/en_sysclk
add wave -noupdate -group SDA_HANDLING_MUX /I3C_TOP_TB/DUT/sda_handling_mode_mux/data_in
add wave -noupdate -group SDA_HANDLING_MUX /I3C_TOP_TB/DUT/sda_handling_mode_mux/ctrl_sel
add wave -noupdate -group SDA_HANDLING_MUX /I3C_TOP_TB/DUT/sda_handling_mode_mux/data_out
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/i_handling_s_data
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/i_handling_sel_pp_od
add wave -noupdate -group SDA_HANDLING -color Yellow /I3C_TOP_TB/DUT/u_sda_handling/i_handling_pp_en
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/sda
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/o_handling_s_data
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/open_drain_out
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/push_pull_out
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/open_drain_in
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/push_pull_in
add wave -noupdate -group SDA_HANDLING /I3C_TOP_TB/DUT/u_sda_handling/push_pull_enable
add wave -noupdate -group SCL_PP_MODE_MUX /I3C_TOP_TB/DUT/scl_pp_od_mode_mux/data_in
add wave -noupdate -group SCL_PP_MODE_MUX /I3C_TOP_TB/DUT/scl_pp_od_mode_mux/ctrl_sel
add wave -noupdate -group SCL_PP_MODE_MUX /I3C_TOP_TB/DUT/scl_pp_od_mode_mux/data_out
add wave -noupdate -group SCL_PP_OD_MUX /I3C_TOP_TB/DUT/scl_pp_od_mux/data_in
add wave -noupdate -group SCL_PP_OD_MUX /I3C_TOP_TB/DUT/scl_pp_od_mux/ctrl_sel
add wave -noupdate -group SCL_PP_OD_MUX /I3C_TOP_TB/DUT/scl_pp_od_mux/data_out
add wave -noupdate -group SCL_PP_HDR_MUX /I3C_TOP_TB/DUT/scl_pp_od_hdr_mux/data_in
add wave -noupdate -group SCL_PP_HDR_MUX /I3C_TOP_TB/DUT/scl_pp_od_hdr_mux/ctrl_sel
add wave -noupdate -group SCL_PP_HDR_MUX /I3C_TOP_TB/DUT/scl_pp_od_hdr_mux/data_out
add wave -noupdate -group regf_special_data_hdr_mux /I3C_TOP_TB/DUT/regf_special_data_hdr_mux/BUS_WIDTH
add wave -noupdate -group regf_special_data_hdr_mux /I3C_TOP_TB/DUT/regf_special_data_hdr_mux/SEL
add wave -noupdate -group regf_special_data_hdr_mux /I3C_TOP_TB/DUT/regf_special_data_hdr_mux/data_in
add wave -noupdate -group regf_special_data_hdr_mux /I3C_TOP_TB/DUT/regf_special_data_hdr_mux/ctrl_sel
add wave -noupdate -group regf_special_data_hdr_mux /I3C_TOP_TB/DUT/regf_special_data_hdr_mux/data_out
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/o_txrx_addr_ccc
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/Direct_Broadcast_n
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/Direct_Broadcast_n_del
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/target_addres
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/first_time
add wave -noupdate -expand -group CCC -radix unsigned /I3C_TOP_TB/DUT/CCC_Handler/current_state
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/i_rx_mode_done
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/i_rx_pre
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/o_rx_en
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/o_rx_mode
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/i_tx_mode_done
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/i_sclstall_stall_done
add wave -noupdate -expand -group CCC /I3C_TOP_TB/DUT/CCC_Handler/i_frmcnt_last_frame
add wave -noupdate /I3C_TOP_TB/DUT/CCC_Handler/pulse_counter
add wave -noupdate /I3C_TOP_TB/DUT/CCC_Handler/o_sclstall_en
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {9425000000 ps} 0} {{Cursor 4} {7047773996 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 202
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
WaveRestoreZoom {8985591618 ps} {9731686210 ps}

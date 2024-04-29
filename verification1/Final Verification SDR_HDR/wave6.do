onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 24 -expand -group SDA /SDR_HDR_TB/sda_tb
add wave -noupdate -height 24 -expand -group SDA /SDR_HDR_TB/sda_drive
add wave -noupdate -height 24 -expand -group {Clock and SCL} /SDR_HDR_TB/i_clk_tb
add wave -noupdate -height 24 -expand -group {Clock and SCL} -color Cyan /SDR_HDR_TB/DUT/u_scl_generation/o_scl
add wave -noupdate -height 24 -expand -group {Clock and SCL} /SDR_HDR_TB/DUT/u_scl_generation/o_scl_pos_edge
add wave -noupdate -height 24 -expand -group {Clock and SCL} /SDR_HDR_TB/DUT/u_scl_generation/o_scl_neg_edge
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_engine_MODE
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/i_regf_clk
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_cccnt_RnW
add wave -noupdate -height 24 -group REGFILE -radix unsigned /SDR_HDR_TB/DUT/i_regf_wr_address_config
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_cccnt_WROC
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_cccnt_TOC
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_engine_CP
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_ser_rx_tx
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/i_regf_rd_en
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/i_regf_wr_en
add wave -noupdate -height 24 -group REGFILE -radix unsigned /SDR_HDR_TB/DUT/u_reg_file/i_regf_addr
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/i_regf_data_wr
add wave -noupdate -height 24 -group REGFILE -radix unsigned /SDR_HDR_TB/DUT/u_reg_file/i_engine_configuration
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/o_regf_data_rd
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/DWORD_0_Vector
add wave -noupdate -height 24 -group REGFILE /SDR_HDR_TB/DUT/u_reg_file/DWORD_1_Vector
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1007]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1006]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1005]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1004]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1003]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1002]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1001]}
add wave -noupdate -height 24 -group REGFILE -group CONFIG_MEMORY -radix binary {/SDR_HDR_TB/DUT/u_reg_file/reg_array[1000]}
add wave -noupdate -height 24 -group {Enable signals} /SDR_HDR_TB/i_controller_en_tb
add wave -noupdate -height 24 -group {Enable signals} /SDR_HDR_TB/i_hdr_en_tb
add wave -noupdate -height 24 -group {Enable signals} /SDR_HDR_TB/DUT/u_i3c_engine/o_enthdr_en
add wave -noupdate -height 24 -group {Enable signals} /SDR_HDR_TB/DUT/u_i3c_engine/o_hdrengine_en
add wave -noupdate -height 20 -group {I3C_engine states} /SDR_HDR_TB/DUT/u_i3c_engine/state
add wave -noupdate -height 20 -expand -group {ENTHDR states} /SDR_HDR_TB/DUT/u_enthdr/state
add wave -noupdate -color Cyan /SDR_HDR_TB/DUT/u_enthdr/o_tx_en
add wave -noupdate /SDR_HDR_TB/DUT/u_enthdr/o_tx_mode
add wave -noupdate /SDR_HDR_TB/DUT/u_enthdr/o_rx_en
add wave -noupdate /SDR_HDR_TB/DUT/u_enthdr/o_rx_mode
add wave -noupdate -height 24 -expand -group {TX signals} -color Magenta /SDR_HDR_TB/DUT/u_i3c_engine/i_tx_mode_done
add wave -noupdate -height 24 -expand -group {TX signals} -color Cyan /SDR_HDR_TB/DUT/u_i3c_engine/o_tx_en
add wave -noupdate -height 24 -expand -group {TX signals} /SDR_HDR_TB/DUT/u_enthdr/o_tx_mode
add wave -noupdate -height 24 -expand -group {TX signals} /SDR_HDR_TB/DUT/u_controller_tx/i_ser_mode
add wave -noupdate -height 24 -expand -group {TX signals} /SDR_HDR_TB/DUT/u_controller_tx/i_ser_count
add wave -noupdate -height 24 -expand -group {TX signals} /SDR_HDR_TB/DUT/u_controller_tx/i_ser_count_done
add wave -noupdate -height 24 -expand -group {TX signals} /SDR_HDR_TB/DUT/u_controller_tx/i_ser_regf_data
add wave -noupdate -color Cyan /SDR_HDR_TB/DUT/u_controller_tx/i_ser_en
add wave -noupdate -height 24 -expand -group {RX signals} /SDR_HDR_TB/DUT/u_enthdr/i_rx_ack_nack
add wave -noupdate -height 24 -expand -group {RX signals} /SDR_HDR_TB/DUT/u_enthdr/o_rx_en
add wave -noupdate -height 24 -expand -group {RX signals} /SDR_HDR_TB/DUT/u_enthdr/o_rx_mode
add wave -noupdate -height 24 -group {done signals} /SDR_HDR_TB/DUT/u_enthdr/o_i3cengine_done
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/i_i3cengine_hdrengine_en
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/i_ccc_done
add wave -noupdate -height 24 -group {HDR engine} -color Magenta /SDR_HDR_TB/DUT/u_hdr_engine/i_ddr_mode_done
add wave -noupdate -height 24 -group {HDR engine} -color White /SDR_HDR_TB/DUT/u_hdr_engine/o_i3cengine_hdrengine_done
add wave -noupdate -height 24 -group {HDR engine} -color Cyan /SDR_HDR_TB/DUT/u_hdr_engine/o_ddrmode_en
add wave -noupdate -height 24 -group {HDR engine} -color Yellow /SDR_HDR_TB/DUT/u_hdr_engine/i_TOC
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/i_CP
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/current_state
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/next_state
add wave -noupdate -height 24 -group {HDR engine} /SDR_HDR_TB/DUT/u_hdr_engine/o_ccc_en
add wave -noupdate -height 24 -group TB /SDR_HDR_TB/DUT/i_regf_config
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/i_sdr_ctrl_clk
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/i_sdr_ctrl_rst_n
add wave -noupdate -height 24 -group SCL -color Yellow /SDR_HDR_TB/DUT/u_scl_generation/i_sdr_scl_gen_pp_od
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/i_scl_gen_stall
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/i_sdr_ctrl_scl_idle
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/i_timer_cas
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/o_scl_pos_edge
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/o_scl_neg_edge
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/o_scl
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/state
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/LOW
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/HIGH
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/count
add wave -noupdate -height 24 -group SCL /SDR_HDR_TB/DUT/u_scl_generation/switch
add wave -noupdate /SDR_HDR_TB/DUT/i_sdr_rst_n
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {42372260192 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 228
configure wave -valuecolwidth 121
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
configure wave -timelineunits us
update
WaveRestoreZoom {26597653632 ps} {61882145408 ps}

onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /CCC_Handler_tb/DUT0/o_tx_en
add wave -noupdate -radix unsigned /CCC_Handler_tb/DUT0/o_tx_mode
add wave -noupdate /CCC_Handler_tb/DUT0/o_rx_en
add wave -noupdate -color {Violet Red} -radix unsigned /CCC_Handler_tb/DUT0/o_rx_mode
add wave -noupdate /CCC_Handler_tb/DUT0/i_rx_pre
add wave -noupdate /CCC_Handler_tb/DUT0/o_frmcnt_Direct_Broadcast_n
add wave -noupdate /CCC_Handler_tb/DUT0/i_engine_en
add wave -noupdate /CCC_Handler_tb/DUT1/o_scl
add wave -noupdate /CCC_Handler_tb/DUT0/o_sclstall_en
add wave -noupdate /CCC_Handler_tb/DUT0/o_sclstall_code
add wave -noupdate /CCC_Handler_tb/DUT0/i_tx_mode_done
add wave -noupdate /CCC_Handler_tb/DUT0/i_sclstall_stall_done
add wave -noupdate /CCC_Handler_tb/DUT0/i_rx_mode_done
add wave -noupdate /CCC_Handler_tb/DUT2/i_sys_clk
add wave -noupdate /CCC_Handler_tb/DUT0/i_engine_en
add wave -noupdate /CCC_Handler_tb/DUT9/o_crc_en
add wave -noupdate /CCC_Handler_tb/DUT0/i_rx_error
add wave -noupdate -color Gold -radix unsigned /CCC_Handler_tb/DUT0/next_state
add wave -noupdate -color Gold -radix unsigned /CCC_Handler_tb/DUT0/current_state
add wave -noupdate /CCC_Handler_tb/DUT9/i_sdahnd_rx_sda
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {31147150 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
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
WaveRestoreZoom {31146446 ns} {31148076 ns}
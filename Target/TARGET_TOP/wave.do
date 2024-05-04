onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {BUS} -color Magenta /nt_target_tb/DUT4/i_sclgen_scl
add wave -noupdate -expand -group {BUS} -color Wheat /nt_target_tb/DUT4/i_sdahnd_rx_sda
add wave -noupdate -expand -group {BUS} -color Red /nt_target_tb/DUT5/o_sdahnd_tgt_serial_data
add wave -noupdate -expand -group {MODE DONE} /nt_target_tb/DUT0/i_tx_mode_done
add wave -noupdate /nt_target_tb/DUT0/i_rx_mode_done
add wave -noupdate /nt_target_tb/DUT0/o_engine_done
add wave -noupdate -expand -group {ENABLE} /nt_target_tb/DUT0/i_engine_en
add wave -noupdate -expand -group {ENABLE} /nt_target_tb/DUT0/o_tx_en
add wave -noupdate -expand -group {ENABLE} /nt_target_tb/DUT4/i_ddrccc_rx_en
add wave -noupdate -expand -group {MODE} /nt_target_tb/DUT0/o_tx_mode
add wave -noupdate -expand -group {MODE} /nt_target_tb/DUT4/i_ddrccc_rx_mode
add wave -noupdate -expand -group {FLAGS} /nt_target_tb/DUT0/i_rx_pre
add wave -noupdate -expand -group {FLAGS} /nt_target_tb/DUT0/i_rx_error
add wave -noupdate -expand -group {FLAGS} /nt_target_tb/DUT0/i_rx_ddrccc_rnw
add wave -noupdate -expand -group {FLAGS} /nt_target_tb/DUT0/i_frmcnt_last
add wave -noupdate -expand -group {FLAGS} /nt_target_tb/DUT4/o_engine_decision
add wave -noupdate -expand -group {NT_states} -radix hexadecimal /nt_target_tb/DUT0/next_state
add wave -noupdate -expand -group {NT_states} -radix hexadecimal /nt_target_tb/DUT0/current_state
add wave -noupdate -expand -group {REG_FILE} /nt_target_tb/DUT0/o_regf_addr
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1384 ps} 0}
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
configure wave -timelineunits ps
update
WaveRestoreZoom {1140 ps} {1388 ps}

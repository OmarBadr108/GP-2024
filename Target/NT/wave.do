onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {BUS
add wave -noupdate -expand -group {BUS
add wave -noupdate -expand -group {BUS
add wave -noupdate -expand -group {MODE DONE
add wave -noupdate /nt_target_tb/DUT0/i_rx_mode_done
add wave -noupdate /nt_target_tb/DUT0/o_engine_done
add wave -noupdate -expand -group {ENABLE
add wave -noupdate -expand -group {ENABLE
add wave -noupdate -expand -group {ENABLE
add wave -noupdate -expand -group {MODE
add wave -noupdate -expand -group {MODE
add wave -noupdate -expand -group {FLAGS
add wave -noupdate -expand -group {FLAGS
add wave -noupdate -expand -group {FLAGS
add wave -noupdate -expand -group {FLAGS
add wave -noupdate -expand -group {FLAGS
add wave -noupdate -expand -group {NT_states
add wave -noupdate -expand -group {NT_states
add wave -noupdate -expand -group {REG_FILE
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
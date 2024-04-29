onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top_test/dut/dut4/o_cnt_bit_count
add wave -noupdate /top_test/dut/dut3/o_scl
add wave -noupdate /top_test/dut/dut0/current_state
add wave -noupdate /top_test/dut/dut0/o_engine_done
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {0 ps} {2140 ps}

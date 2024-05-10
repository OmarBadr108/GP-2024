
############################  Search PATH ################################

set PROJECT_PATH /home/IC/Labs/GP/I3C_TOP_2024/rtl
set LIB_PATH     /home/IC/Labs/GP/I3C_TOP_2024/std_cells

lappend search_path $LIB_PATH
lappend search_path $PROJECT_PATH


########################### Define Top Module ############################
                                                   
set top_module I3C_TOP

######################### Formality Setup File ###########################

set synopsys_auto_setup true

set_svf $top_module.svf


####################### Read Reference tech libs ########################
 

set SSLIB "scmetro_tsmc_cl013g_rvt_ss_1p08v_125c.db"
set TTLIB "scmetro_tsmc_cl013g_rvt_tt_1p2v_25c.db"
set FFLIB "scmetro_tsmc_cl013g_rvt_ff_1p32v_m40c.db"

read_db -container Ref [list $SSLIB $TTLIB $FFLIB]

###################  Read Reference Design Files ######################## 
read_verilog -container Ref "bits_counter.v"
read_verilog -container Ref "bits_counter_sdr.v"
read_verilog -container Ref "CCC_Handler.v"
read_verilog -container Ref "clk_divider.v"
read_verilog -container Ref "controller_crh.v"
read_verilog -container Ref "controller_RX.v"
read_verilog -container Ref "controller_TX.v"
read_verilog -container Ref "dynamic_address_assignment.v"
read_verilog -container Ref "ENTHDR.v"
read_verilog -container Ref "FRAME_COUNTER.v"

read_verilog -container Ref "frame_counter_sdr.v"
read_verilog -container Ref "gen_mux.v"
read_verilog -container Ref "HDR_Engine.v"
read_verilog -container Ref "hot_join.v"
read_verilog -container Ref "i2c_legacy_mode.v"
read_verilog -container Ref "i3c_timer_fsm.v"
read_verilog -container Ref "IBI.v"
read_verilog -container Ref "main_ctrl_unit.v"

read_verilog -container Ref "new_i3c_engine.v"
read_verilog -container Ref "Normal_Transaction.v"
read_verilog -container Ref "open_drain_behav_model.v"
read_verilog -container Ref "push_pull_behav_model.v"
read_verilog -container Ref "reg_file.v"
read_verilog -container Ref "Rx.v"
read_verilog -container Ref "scl_generation.v"
read_verilog -container Ref "scl_staller.v"

read_verilog -container Ref "sda_handling.v"
read_verilog -container Ref "sdr_mode.v"
read_verilog -container Ref "staller.v"
read_verilog -container Ref "timings.v"
read_verilog -container Ref "top_for_crh_test.v"
read_verilog -container Ref "top_for_hj_test.v"
read_verilog -container Ref "tri_state_buf.v"
read_verilog -container Ref "tri_state_buf_n.v"
read_verilog -container Ref "Tx.v"

read_verilog -container Ref "i3c_top.v"

######################## set the top Reference Design ######################## 

set_reference_design I3C_TOP
set_top I3C_TOP

####################### Read Implementation tech libs ######################## 

read_db -container Imp [list $SSLIB $TTLIB $FFLIB]

#################### Read Implementation Design Files ######################## 

read_verilog -container Imp -netlist "/home/IC/Labs/GP/I3C_TOP_2024/I3C_TOP_syn.v"

####################  set the top Implementation Design ######################

set_implementation_design I3C_TOP
set_top I3C_TOP


## matching Compare points
match

## verify
set successful [verify]
if {!$successful} {
diagnose
analyze_points -failing
}

report_passing_points > "reports/passing_points.rpt"
report_failing_points > "reports/failing_points.rpt"
report_aborted_points > "reports/aborted_points.rpt"
report_unverified_points > "reports/unverified_points.rpt"


start_gui
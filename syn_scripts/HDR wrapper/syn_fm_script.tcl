
############################  Search PATH ################################

set PROJECT_PATH /home/IC/Labs/GP/NT_wrapper/rtl
set LIB_PATH     /home/IC/Labs/GP/NT_wrapper/std_cells

lappend search_path $LIB_PATH
lappend search_path $PROJECT_PATH


########################### Define Top Module ############################
                                                   
set top_module nt_top

######################### Formality Setup File ###########################

set synopsys_auto_setup true

set_svf $top_module.svf


####################### Read Reference tech libs ########################
 

set SSLIB "scmetro_tsmc_cl013g_rvt_ss_1p08v_125c.db"
set TTLIB "scmetro_tsmc_cl013g_rvt_tt_1p2v_25c.db"
set FFLIB "scmetro_tsmc_cl013g_rvt_ff_1p32v_m40c.db"

read_db -container Ref [list $SSLIB $TTLIB $FFLIB]

###################  Read Reference Design Files ######################## 
read_verilog -container Ref "Normal_Transaction.v"
read_verilog -container Ref "bit_counter.v"
read_verilog -container Ref "frame_counter.v"
read_verilog -container Ref "rx.v"
read_verilog -container Ref "scl_generation.v"
read_verilog -container Ref "staller.v"
read_verilog -container Ref "Tx.v"


read_verilog -container Ref "nt_top.v"

######################## set the top Reference Design ######################## 

set_reference_design nt_top
set_top nt_top

####################### Read Implementation tech libs ######################## 

read_db -container Imp [list $SSLIB $TTLIB $FFLIB]

#################### Read Implementation Design Files ######################## 

read_verilog -container Imp -netlist "/home/IC/Labs/GP/NT_wrapper/nt_top.v"

####################  set the top Implementation Design ######################

set_implementation_design nt_top
set_top nt_top


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


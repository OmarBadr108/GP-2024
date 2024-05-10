
########################### Define Top Module ############################
                                                   
set top_module I3C_TOP

##################### Define Working Library Directory ######################
                                                   
define_design_lib work -path ./work

############################# Formality Setup File ##########################
#set synopsys_auto_setup true
                                                   
set_svf $top_module.svf



################## Design Compiler Library Files #setup ######################

puts "###########################################"
puts "#      #setting Design Libraries          #"
puts "###########################################"

#Add the path of the libraries and RTL files to the search_path variable

set PROJECT_PATH /home/IC/Labs/GP/I3C_TOP_2024/rtl
set LIB_PATH     /home/IC/Labs/GP/I3C_TOP_2024/std_cells

lappend search_path $LIB_PATH
lappend search_path $PROJECT_PATH


set SSLIB "scmetro_tsmc_cl013g_rvt_ss_1p08v_125c.db"
set TTLIB "scmetro_tsmc_cl013g_rvt_tt_1p2v_25c.db"
set FFLIB "scmetro_tsmc_cl013g_rvt_ff_1p32v_m40c.db"

## Standard Cell libraries 
set target_library [list $SSLIB $TTLIB $FFLIB]

## Standard Cell & Hard Macros libraries 
set link_library [list * $SSLIB $TTLIB $FFLIB]  

######################## Reading RTL Files #################################

puts "###########################################"
puts "#             Reading RTL Files           #"
puts "###########################################"

set file_format verilog


analyze -format $file_format bits_counter.v
analyze -format $file_format bits_counter_sdr.v
analyze -format $file_format CCC_Handler.v
analyze -format $file_format clk_divider.v
analyze -format $file_format controller_crh.v
analyze -format $file_format controller_RX.v
analyze -format $file_format controller_TX.v
analyze -format $file_format dynamic_address_assignment.v
analyze -format $file_format ENTHDR.v
analyze -format $file_format FRAME_COUNTER.v

analyze -format $file_format frame_counter_sdr.v
analyze -format $file_format gen_mux.v
analyze -format $file_format HDR_Engine.v
analyze -format $file_format hot_join.v
analyze -format $file_format i2c_legacy_mode.v
analyze -format $file_format i3c_timer_fsm.v
analyze -format $file_format IBI.v
analyze -format $file_format main_ctrl_unit.v

analyze -format $file_format new_i3c_engine.v
analyze -format $file_format Normal_Transaction.v
analyze -format $file_format open_drain_behav_model.v
analyze -format $file_format push_pull_behav_model.v
analyze -format $file_format reg_file.v
analyze -format $file_format Rx.v
analyze -format $file_format scl_generation.v
analyze -format $file_format scl_staller.v

analyze -format $file_format sda_handling.v
analyze -format $file_format sdr_mode.v
analyze -format $file_format staller.v
analyze -format $file_format timings.v
analyze -format $file_format top_for_crh_test.v
analyze -format $file_format top_for_hj_test.v
analyze -format $file_format tri_state_buf.v
analyze -format $file_format tri_state_buf_n.v
analyze -format $file_format Tx.v

#SYS_TOP
analyze -format $file_format i3c_top.v

elaborate -lib WORK I3C_TOP

###################### Defining toplevel ###################################

current_design $top_module

#################### Liniking All The Design Parts #########################
puts "###############################################"
puts "######## Liniking All The Design Parts ########"
puts "###############################################"

link 

#################### Liniking All The Design Parts #########################
puts "###############################################"
puts "######## checking design consistency ##########"
puts "###############################################"

check_design >> check_design.rpt

#################### Define Design Constraints #########################
puts "###############################################"
puts "############ Design Constraints #### ##########"
puts "###############################################"

source -echo ./cons.tcl

###################### Mapping and optimization ########################
puts "###############################################"
puts "########## Mapping & Optimization #############"
puts "###############################################"

compile 

##################### Close Formality Setup file ###########################

set_svf -off

#############################################################################
# Write out files
#############################################################################

write_file -format verilog -hierarchy -output $top_module.ddc
write_file -format verilog -hierarchy -output I3C_TOP_syn.v
write_sdf  $top_module.sdf
write_sdc  -nosplit $top_module.sdc

####################### reporting ##########################################

report_area -hierarchy > area.rpt
report_power -hierarchy > power.rpt
report_timing -delay_type min -max_paths 20 > hold.rpt
report_timing -delay_type max -max_paths 20 > setup.rpt
report_clock -attributes > clocks.rpt
report_timing -attributes
report_constraint -all_violators -nosplit > constraints.rpt

############################################################################
# DFT Preparation Section
############################################################################

set flops_per_chain 100

set num_flops [sizeof_collection [all_registers -edge_triggered]]

set num_chains [expr $num_flops / $flops_per_chain + 1 ]

################# starting graphical user interface #######################

#gui_start

#exit

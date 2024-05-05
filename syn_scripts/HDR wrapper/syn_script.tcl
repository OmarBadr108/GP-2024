
########################### Define Top Module ############################
                                                   
set top_module nt_top

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

set PROJECT_PATH /home/IC/Labs/GP/NT_wrapper/rtl
set LIB_PATH     /home/IC/Labs/GP/NT_wrapper/std_cells

lappend search_path $LIB_PATH
lappend search_path $PROJECT_PATH

#lappend search_path $PROJECT_PATH/RTL/ASYNC_FIFO
#lappend search_path $PROJECT_PATH/RTL/Clock_Divider
#lappend search_path $PROJECT_PATH/RTL/Clock_Gating
#lappend search_path $PROJECT_PATH/RTL/DATA_SYNC
#lappend search_path $PROJECT_PATH/RTL/RegFile
#lappend search_path $PROJECT_PATH/RTL/PULSE_GEN
#lappend search_path $PROJECT_PATH/RTL/RST_SYNC
#lappend search_path $PROJECT_PATH/RTL/SYS_CTRL
#lappend search_path $PROJECT_PATH/RTL/CLKDIV_MUX
#lappend search_path $PROJECT_PATH/RTL/UART/UART_RX
#lappend search_path $PROJECT_PATH/RTL/UART/UART_TX
#lappend search_path $PROJECT_PATH/RTL/UART/UART_TOP
#lappend search_path $PROJECT_PATH/RTL/Top

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

#Normal_transaction
analyze -format $file_format Normal_Transaction.v
analyze -format $file_format bit_counter.v
analyze -format $file_format frame_counter.v
analyze -format $file_format rx.v
analyze -format $file_format scl_generation.v
analyze -format $file_format staller.v
analyze -format $file_format Tx.v

#SYS_TOP
analyze -format $file_format nt_top.v

elaborate -lib WORK nt_top

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
write_file -format verilog -hierarchy -output $top_module.v
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

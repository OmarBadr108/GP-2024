
####################################################################################
# Constraints
# ----------------------------------------------------------------------------
#
# 0. Design Compiler variables
#
# 1. Master Clock Definitions
#
# 2. Generated Clock Definitions
#
# 3. Clock Uncertainties
#
# 4. Clock Latencies 
#
# 5. Clock Relationships
#
# 6. set input/output delay on ports
#
# 7. Driving cells
#
# 8. Output load

####################################################################################
           #########################################################
                  #### Section 0 : DC Variables ####
           #########################################################
#################################################################################### 

# Prevent assign statements in the generated netlist (must be applied before compile command)
set_fix_multiple_port_nets -all -buffer_constants -feedthroughs

####################################################################################
           #########################################################
                  #### Section 1 : Clock Definition ####
           #########################################################
set CLK_NAME1 SYS_CLK
set CLK_PER1 20
set CLK_SETUP_SKEW 0.4
set CLK_HOLD_SKEW 0.2
set CLK_LAT 0
set CLK_RISE 0.2
set CLK_FALL 0.2
#################################################################################### 
# 1. Master Clock Definitions
create_clock -name $CLK_NAME1 -period $CLK_PER1 -waveform "0 [expr $CLK_PER1/2]" [get_ports i_sys_clk]
 
# 2. Generated Clock Definitions
#create_generated_clock -master_clock $CLK_NAME1 -source [get_ports REF_CLK] \
#                       -name "ALU_CLK" [get_port U0_CLK_GATE/GATED_CLK] \
#                       -divide_by 1

# 3. Clock Latencies
set_clock_latency $CLK_LAT [get_clocks $CLK_NAME1]

# 4. Clock Uncertainties
set_clock_uncertainty -setup $CLK_SETUP_SKEW [get_clocks $CLK_NAME1]
set_clock_uncertainty -hold $CLK_HOLD_SKEW  [get_clocks $CLK_NAME1]

# 4. Clock Transitions

####################################################################################
set_clock_transition -rise $CLK_RISE  [get_clocks $CLK_NAME1]
set_clock_transition -fall $CLK_FALL  [get_clocks $CLK_NAME1]

set_dont_touch_network {SYS_CLK RST}

####################################################################################
           #########################################################
             #### Section 2 : Clocks Relationship ####
           #########################################################
####################################################################################
#set_clock_groups -asynchronous -group [get_clocks "$CLK_NAME2 TX_CLK RX_CLK"] -group [get_clocks "ALU_CLK $CLK_NAME1"] 

  

####################################################################################
           #########################################################
             #### Section 3 : set input/output delay on ports ####
           #########################################################
####################################################################################
#Constrain Input Paths
set in_delay  [expr 0.2*$CLK_PER1]

set_input_delay $in_delay -clock SYS_CLK [get_port i_engine_en]           
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_toc]                         
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_dev_index]               
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_short_read]                 
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_wroc]                        
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_wr_rd_bit]              
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_cmd_attr]                      
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_dtt]               
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_tx_parallel_data]   
set_input_delay $in_delay -clock SYS_CLK [get_port i_crc_crc_value]              
set_input_delay $in_delay -clock SYS_CLK [get_port i_sdahnd_rx_sda]              
set_input_delay $in_delay -clock SYS_CLK [get_port i_crc_valid]               
set_input_delay $in_delay -clock SYS_CLK [get_port i_sdr_ctrl_scl_idle]              
set_input_delay $in_delay -clock SYS_CLK [get_port i_timer_cas]                  

set_input_delay $in_delay -clock SYS_CLK [get_port i_ccc_Direct_Broadcast_n]                     
set_input_delay $in_delay -clock SYS_CLK [get_port i_regf_DATA_LEN]                     




#Constrain Output Paths

set out_delay [expr 0.2*$CLK_PER1]

set_output_delay $out_delay -clock SYS_CLK [get_port o_regf_wr_en]            
set_output_delay $out_delay -clock SYS_CLK [get_port o_regf_rd_en]                   
set_output_delay $out_delay -clock SYS_CLK [get_port o_regf_addr]                    
set_output_delay $out_delay -clock SYS_CLK [get_port o_engine_done]                    
set_output_delay $out_delay -clock SYS_CLK [get_port o_regf_abort]                   
set_output_delay $out_delay -clock SYS_CLK [get_port o_regf_error_type]               
set_output_delay $out_delay -clock SYS_CLK [get_port o_crc_en]                   
set_output_delay $out_delay -clock SYS_CLK [get_port o_crc_parallel_data]       
set_output_delay $out_delay -clock SYS_CLK [get_port o_sdahnd_serial_data]        
set_output_delay $out_delay -clock SYS_CLK [get_port o_crc_data_valid]            
set_output_delay $out_delay -clock SYS_CLK [get_port o_regfcrc_rx_data_out]     
set_output_delay $out_delay -clock SYS_CLK [get_port o_scl]                     



####################################################################################
           #########################################################
                  #### Section 4 : Driving cells ####
           #########################################################
####################################################################################
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_engine_en]
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_engine_en]          
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_toc]              
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_dev_index]        
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_short_read]       
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_wroc]             
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_wr_rd_bit]        
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_cmd_attr]         
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_dtt]              
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_tx_parallel_data] 
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_crc_crc_value]         
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_sdahnd_rx_sda]         
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_crc_valid]             
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_sdr_ctrl_scl_idle]     
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_timer_cas]             
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_ccc_Direct_Broadcast_n]
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_DATA_LEN]         

####################################################################################
           #########################################################
                  #### Section 5 : Output load ####
           #########################################################
####################################################################################


set_load 0.5 [get_port o_regf_wr_en]         
set_load 0.5 [get_port o_regf_rd_en]         
set_load 0.5 [get_port o_regf_addr]          
set_load 0.5 [get_port o_engine_done]        
set_load 0.5 [get_port o_regf_abort]         
set_load 0.5 [get_port o_regf_error_type]    
set_load 0.5 [get_port o_crc_en]             
set_load 0.5 [get_port o_crc_parallel_data]  
set_load 0.5 [get_port o_sdahnd_serial_data] 
set_load 0.5 [get_port o_crc_data_valid]     
set_load 0.5 [get_port o_regfcrc_rx_data_out]
set_load 0.5 [get_port o_scl]                
####################################################################################
           #########################################################
                 #### Section 6 : Operating Condition ####
           #########################################################
####################################################################################

# Define the Worst Library for Max(#setup) analysis
# Define the Best Library for Min(hold) analysis

set_operating_conditions -min_library "scmetro_tsmc_cl013g_rvt_ff_1p32v_m40c" -min "scmetro_tsmc_cl013g_rvt_ff_1p32v_m40c" -max_library "scmetro_tsmc_cl013g_rvt_ss_1p08v_125c" -max "scmetro_tsmc_cl013g_rvt_ss_1p08v_125c"

####################################################################################
           #########################################################
                  #### Section 7 : wireload Model ####
           #########################################################
####################################################################################

set_wire_load_model -name tsmc13_wl10 -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c

####################################################################################



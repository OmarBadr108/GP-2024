
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
set CLK_NAME1 i_sdr_clk
set CLK_PER1 20
set CLK_SETUP_SKEW 0.4
set CLK_HOLD_SKEW 0.2
set CLK_LAT 0
set CLK_RISE 0.2
set CLK_FALL 0.2
#################################################################################### 
# 1. Master Clock Definitions
create_clock -name $CLK_NAME1 -period $CLK_PER1 -waveform "0 [expr $CLK_PER1/2]" [get_ports i_sdr_clk]
 
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

set_dont_touch_network {i_sdr_clk i_sdr_rst_n}

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

set_input_delay $in_delay -clock i_sdr_clk [get_port i_controller_en]           
set_input_delay $in_delay -clock i_sdr_clk [get_port i_i3c_i2c_sel]                         
set_input_delay $in_delay -clock i_sdr_clk [get_port i_ccc_en_dis_hj]               
set_input_delay $in_delay -clock i_sdr_clk [get_port i_sclgen_rst_n]                 
set_input_delay $in_delay -clock i_sdr_clk [get_port i_regf_config]                        
set_input_delay $in_delay -clock i_sdr_clk [get_port i_data_config_mux_sel]              
set_input_delay $in_delay -clock i_sdr_clk [get_port i_regf_wr_address_config]   
set_input_delay $in_delay -clock i_sdr_clk [get_port i_regf_wr_en_config]   
set_input_delay $in_delay -clock i_sdr_clk [get_port i_regf_rd_en_config]   

#inout port is constrained as input ?                   
set_input_delay $in_delay -clock i_sdr_clk [get_port sda]    




#Constrain Output Paths

set out_delay [expr 0.2*$CLK_PER1]

set_output_delay $out_delay -clock i_sdr_clk [get_port o_ctrl_done]            
set_output_delay $out_delay -clock i_sdr_clk [get_port o_sdr_rx_valid]                   
set_output_delay $out_delay -clock i_sdr_clk [get_port scl]  

####################################################################################
           #########################################################
                  #### Section 4 : Driving cells ####
           #########################################################
####################################################################################

set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_controller_en]
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_i3c_i2c_sel]          
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_ccc_en_dis_hj]              
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_sclgen_rst_n]        
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_config]       
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_data_config_mux_sel]             
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_wr_address_config]
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_wr_en_config]             
set_driving_cell -library scmetro_tsmc_cl013g_rvt_ss_1p08v_125c -lib_cell BUFX2M -pin Y [get_port i_regf_rd_en_config]
  
####################################################################################
           #########################################################
                  #### Section 5 : Output load ####
           #########################################################
####################################################################################


set_load 0.5 [get_port o_ctrl_done]         
set_load 0.5 [get_port o_sdr_rx_valid]         
set_load 0.5 [get_port scl]          

           
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




vlib work
vmap work work
vlog -coveropt 3 +cover +acc SDR_HDR_TOP.sv SDR_HDR_TB_FINAL.sv new_i3c_engine.v sdr_mode.v i2c_legacy_mode.v dynamic_address_assignment.v hot_join.v IBI.v controller_crh.v i3c_timer_fsm.v controller_tx.v bits_counter.v controller_RX.v frame_counter.v sda_handling.v scl_generation.v reg_file_new.v  clk_divider.v HDR_Engine.v gen_mux.v pkg.sv open_drain_behav_model.v push_pull_behav_model.v scl_staller.v ENTHDR.v tri_state_buf.v tri_state_buf_n.v +cover -covercells 
vsim -voptargs=+acc work.SDR_HDR_TB_FINAL -cover
coverage save TB_COV.ucdb -onexit
vcover report -html TB_COV.ucdb
package Normal_Transaction_pkg ;

	class Rand_Inputs ;
	    //-----------------ddr-------------// 
		
		rand bit           	     i_engine_en_tb;
		rand bit           		 i_regf_toc_tb;
		rand bit  [4:0]     	 i_regf_dev_index_tb;
		rand bit            	 i_regf_short_read_tb;
		rand bit            	 i_regf_wroc_tb;
		rand bit            	 i_regf_wr_rd_bit_tb;
		rand bit            	 i_regf_cmd_attr_tb;
		rand bit  [2:0]     	 i_regf_dtt_tb;
		
		constraint dev_index {
			i_regf_dev_index_tb inside {[1:31]} ;
			
			}
			
		/*constraint toc {
			i_regf_toc_tb == 1  ;
			
			}*/
			
		constraint wr_rd_bit {
			if (i_regf_cmd_attr_tb)
			i_regf_wr_rd_bit_tb == 0 ;
			
			}
			
		/*constraint cmd_attr {
			i_regf_cmd_attr_tb == 1;
			}*/
			
			
		constraint engine_en {
			i_engine_en_tb == 1;
			}
			
			
		constraint short_read {
			i_regf_short_read_tb dist {0:=10 , 1:=90};
			}


		

		
		//------------tx-----------------//	
		rand bit  [7:0]     	 i_regf_tx_parallel_data_tb;
		rand bit  [4:0]     	 i_crc_crc_value_tb;
		
		
		//-------------rx---------------//
		rand bit              	 i_sdahnd_rx_sda_tb;
		rand bit              	 i_crc_valid_tb;
		 
	    constraint crc_valid {				 //temporary constraint
			i_crc_valid_tb ==1;           
			}
		
		//-------------scl---------------//   
		rand bit          	     i_sdr_ctrl_scl_idle_tb;
		rand bit                i_timer_cas_tb;
		
		constraint forced_zero {
			i_sdr_ctrl_scl_idle_tb ==0;
			i_timer_cas_tb ==0;
			}
		
		//-------------frm_cnt---------------//
		rand bit              i_ccc_Direct_Broadcast_n_tb;
		rand bit   [15:0]     i_regf_DATA_LEN_tb;
		
		constraint Direct_Broadcast {
			i_ccc_Direct_Broadcast_n_tb ==0;
			
			}
			
		constraint DATA_LEN {
			i_regf_DATA_LEN_tb inside {3,4};
			
			}
			
		//----------internal----------------//
		rand bit               check_error;
		rand bit               nack_error;
		rand bit               abort_error;
		
		constraint error {
			check_error dist {0:=80 , 1:=20};
			if (nack_error && abort_error)
				check_error == 'b0;
				
			nack_error dist {0:=70 , 1:=30};
			
			abort_error dist {0:=70 , 1:=30};
			
				}
		
		constraint dtt {
			i_regf_dtt_tb inside {[1:4]} ;
			
			if(check_error && abort_error)
				i_regf_dtt_tb inside {[3:4]} ;
			}

				
				
			
			
	endclass
	
endpackage
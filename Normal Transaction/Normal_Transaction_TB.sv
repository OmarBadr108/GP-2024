 import Normal_Transaction_pkg ::*;
 `timescale 1ns/1ns
 
 module top_test ();
 
 // Declare inputs and outputs for DUT
  
  //-----------------ddr-------------// 
    reg           	 i_sys_clk_tb;
    reg           	 i_sys_rst_tb;
    reg            	 i_engine_en_tb;
    reg            	 i_regf_toc_tb;
    reg  [4:0]       i_regf_dev_index_tb;
    reg              i_regf_short_read_tb;
    reg              i_regf_wroc_tb;
    reg              i_regf_wr_rd_bit_tb;
    reg              i_regf_cmd_attr_tb;
    reg   [2:0]      i_regf_dtt_tb;
    wire             o_regf_wr_en_tb;
    wire             o_regf_rd_en_tb;
    wire  [9:0]      o_regf_addr_tb;
    wire             o_engine_done_tb;
    wire             o_regf_abort_tb;
    wire  [3:0]      o_regf_error_type_tb;
	
//------------tx-----------------//	
    reg   [7:0]      i_regf_tx_parallel_data_tb;
    reg   [4:0]      i_crc_crc_value_tb;
    wire             o_crc_en_tb;
    wire  [7:0]      o_crc_parallel_data_tb;
    wire             o_sdahnd_serial_data_tb;
   
 //-------------rx---------------//
    reg              i_sdahnd_rx_sda_tb;
	reg              i_crc_valid_tb;
    wire             o_crc_data_valid_tb;
    wire  [7:0]      o_regfcrc_rx_data_out_tb;

//-------------scl---------------//   
    reg              i_sdr_ctrl_scl_idle_tb;
    reg              i_timer_cas_tb;
    wire             o_scl_tb;
   
//-------------frm_cnt---------------//
    reg              i_ccc_Direct_Broadcast_n_tb;
    reg   [15:0]     i_regf_DATA_LEN_tb;
	
	
	
//-------------used_in_tb---------------//
    
    logic   [6:0]     dev_address;
	logic   [63:0]    data_delay;
	bit			 	  check_error;
	bit               nack_error;
	bit               abort_error;
	
	

    // Instantiate DUT
    top dut (
        .i_sys_clk(i_sys_clk_tb),
        .i_sys_rst(i_sys_rst_tb),
        .i_engine_en(i_engine_en_tb),
        .i_regf_toc(i_regf_toc_tb),
        .i_regf_dev_index(i_regf_dev_index_tb),
        .i_regf_short_read(i_regf_short_read_tb),
        .i_regf_wroc(i_regf_wroc_tb),
        .i_regf_wr_rd_bit(i_regf_wr_rd_bit_tb),
        .i_regf_cmd_attr(i_regf_cmd_attr_tb),
        .i_regf_dtt(i_regf_dtt_tb),
        .o_regf_wr_en(o_regf_wr_en_tb),
        .o_regf_rd_en(o_regf_rd_en_tb),
        .o_regf_addr(o_regf_addr_tb),
        .o_engine_done(o_engine_done_tb),
        .o_regf_abort(o_regf_abort_tb),
        .o_regf_error_type(o_regf_error_type_tb),
        .i_regf_tx_parallel_data(i_regf_tx_parallel_data_tb),
        .i_crc_crc_value(i_crc_crc_value_tb),
        .o_crc_en(o_crc_en_tb),
        .o_crc_parallel_data(o_crc_parallel_data_tb),
        .o_sdahnd_serial_data(o_sdahnd_serial_data_tb),
		.i_sdahnd_rx_sda(i_sdahnd_rx_sda_tb),
        .i_crc_valid(i_crc_valid_tb),
        .o_crc_data_valid(o_crc_data_valid_tb),
        .o_regfcrc_rx_data_out(o_regfcrc_rx_data_out_tb),
        .i_sdr_ctrl_scl_idle(i_sdr_ctrl_scl_idle_tb),
        .i_timer_cas(i_timer_cas_tb),
        .o_scl(o_scl_tb),
        .i_ccc_Direct_Broadcast_n(i_ccc_Direct_Broadcast_n_tb),
        .i_regf_DATA_LEN(i_regf_DATA_LEN_tb)
    );

   
 // clock generation
parameter CLK_PERIOD = 20; 	 	 
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;

 
 
 
	

//-----------------------------------OBJECTS------------------------------------// 
	Rand_Inputs nt;
	
	

	initial 
		begin 
		nt =new();
		
		$dumpfile("dump.vcd"); $dumpvars;
		
	 $monitor ("current_state =%d , i_regf_wr_rd_bit_tb = %d , i_regf_dtt_tb = %d , i_regf_cmd_attr_tb = %d , i_regf_DATA_LEN_tb = %d , check_error =%d , abort_error= %d,i_sdahnd_rx_sda_tb=%d at %t",dut.dut0.current_state, i_regf_wr_rd_bit_tb,i_regf_dtt_tb,i_regf_cmd_attr_tb,i_regf_DATA_LEN_tb,check_error,abort_error,i_sdahnd_rx_sda_tb,$time);
	// $monitor ("bitcnt =%b at %t",dut.dut4.o_cnt_bit_count =='d0,$time);
        initialize();
		#(1*CLK_PERIOD);
		
		rsest();
		
		//$display ("ddddi_engine_en_tb =%b",i_engine_en_tb);
		
		//$display ("o_engine_done_tb=%b",o_engine_done_tb);
		
	repeat(100)
		begin
				
			assert (nt.randomize());
			passing_inputs();
		/*	check_error = 1 ;     //activate when needing to check any type of error
			nack_error =  0 ;    //activate when needing to check nack error
			abort_error = 1	;	 //activate when needing to check abort error*/
				//if (i_engine_en_tb)
				//	wait(o_engine_done_tb);
			if (!check_error)
				begin 
				if (!i_regf_cmd_attr_tb)
					begin
						i_regf_tx_parallel_data_tb ='d0;
						@(dut.dut0.current_state =='d6)
						i_sdahnd_rx_sda_tb = 'b0;
					
						@(dut.dut0.current_state =='d9)
						i_sdahnd_rx_sda_tb = 'b1;
					
					
						@(dut.dut0.current_state =='d7);
						i_sdahnd_rx_sda_tb = 'b0;
						
						/*@(dut.dut0.current_state =='d9)
						i_sdahnd_rx_sda_tb = 'b0;*/
					
					
					
						@(dut.dut0.current_state == 'd12);
						i_sdahnd_rx_sda_tb = 1;
					
						//@(dut.dut0.current_state =='d19)
						//i_regf_tx_parallel_data_tb ='d0;
					
						@(dut.dut0.current_state =='d0);
					
					end
				
				else 
					begin
						i_regf_tx_parallel_data_tb ='d0;
						
						@(dut.dut0.current_state =='d6)
						i_sdahnd_rx_sda_tb = 'b0;
						
							if ((i_regf_dtt_tb == 'd3) || (i_regf_dtt_tb == 'd4))
								begin 
									@(dut.dut0.current_state =='d9)
									i_sdahnd_rx_sda_tb = 'b1;
									@(dut.dut0.current_state =='d0);
									//#(10*CLK_PERIOD);
								end
							else 
								@(dut.dut0.current_state =='d0);
						
						
					end
				end
				
				else 
					begin 
						if(nack_error)				
						begin
							@(dut.dut0.current_state =='d6);
							i_sdahnd_rx_sda_tb = 'b1;
							@(dut.dut0.current_state =='d0);
						end
						
						else if (abort_error)
						begin 
							
								i_sdahnd_rx_sda_tb = 'b0;
								@(dut.dut0.current_state =='d15);
								i_sdahnd_rx_sda_tb = 'b1;
								@(dut.dut0.current_state =='d0);
								
							
						end
						
					end
						
					
						
					
					
					
					//$display ("i_engine_en_tb=%b at %t",i_engine_en_tb,$time);
					
					
				//$display("rrrrrrrrrrrrrrrrrrr");
				//$display ("o_engine_done_tb=%b at %t",o_engine_done_tb,$time);
				//$display ("i_engine_en_tb=%b at %t",i_engine_en_tb,$time);
				//wait(!o_engine_done_tb);
				
		end
		
		
	//#(1000*CLK_PERIOD);
		
		
		//@(dut.dut0.current_state =='d0);
		
		$stop;
		
		
		
		
		
	
	

	/*	i_regf_toc_tb = 1;

		i_regf_cmd_attr_tb =1;
		i_regf_wr_rd_bit_tb =0;
		i_engine_en_tb  = 1;
		
		#(2000*CLK_PERIOD)*/
		


		
	
	
	
	
	
	
	
	
	end
	
	
	
//-------------------------------------ASSERTIONS--------------------------------//	
	property check_sys_in_rst_mode ;
	
		@(negedge i_sys_clk_tb)disable iff (i_sys_rst_tb)(!i_sys_rst_tb)-> (o_scl_tb)-> (o_sdahnd_serial_data_tb && (dut.dut0.current_state ==0));
	
	endproperty:check_sys_in_rst_mode
	
	reset_mode: assert property (check_sys_in_rst_mode) 
				$display("reset_mode is SUCCEEDED "); 
		 else 		
				$info ("reset_mode is FAILED") ;

///////////////////////////////////////////////////////////////////////////////////////////////////////////				
	
	      
	
	property regular_write_odd_bytes_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (i_regf_DATA_LEN_tb[0])
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  |-> ##60  zeros_byte_w 
	|-> ##6 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
			
	endproperty:regular_write_odd_bytes_with_no_more_config
		
	regular_write_odd_bytes_1: assert property (regular_write_odd_bytes_with_no_more_config) 
				$display("regular_write_odd_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_write_odd_bytes_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////		


property regular_write_even_bytes_with_no_more_config ;  
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (!(i_regf_DATA_LEN_tb[0]))
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre    
	|-> ##80 fourth_stage_crc_pre_w |-> ##2 token_crc  |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
			
	endproperty:regular_write_even_bytes_with_no_more_config
		
	regular_write_even_bytes_1: assert property (regular_write_even_bytes_with_no_more_config) 
				$display("regular_write_even_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_write_even_bytes_with_no_more_config is FAILED at %0t",$time) ;		

///////////////////////////////////////////////////////////////////////////////////////////////////////////	

property regular_write_odd_bytes_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (i_regf_DATA_LEN_tb[0])
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  |-> ##60  zeros_byte_w 
	|-> ##6 fourth_stage_crc_pre_w |-> ##2 token_crc ##12 (dut.dut0.current_state =='d16) ;
			
	
			
	endproperty:regular_write_odd_bytes_with_coming_config
		
	regular_write_odd_bytes_2: assert property (regular_write_odd_bytes_with_coming_config) 
				$display("regular_write_odd_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_write_odd_bytes_with_coming_config is FAILED at %0t",$time) ;	


///////////////////////////////////////////////////////////////////////////////////////////////////////////

property regular_write_even_bytes_with_coming_config ;  
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (!(i_regf_DATA_LEN_tb[0]))
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre    
	|-> ##80 fourth_stage_crc_pre_w |-> ##2 token_crc  |-> ##12 (dut.dut0.current_state =='d16) ;
			
	
			
	endproperty:regular_write_even_bytes_with_coming_config
		
	regular_write_even_bytes_2: assert property (regular_write_even_bytes_with_coming_config) 
				$display("regular_write_even_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_write_even_bytes_with_coming_config is FAILED at %0t",$time) ;	
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property regular_read_odd_bytes_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (i_regf_DATA_LEN_tb[0])
	&& (i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_read |-> ##22 sec_stage_data_pre  |-> ##58  zeros_byte_r 
	|-> ##6 fourth_stage_crc_pre_r   |-> ##22 (dut.dut0.current_state =='d17) ;
			
	
			
	endproperty:regular_read_odd_bytes_with_no_more_config
		
	regular_read_odd_bytes_1: assert property (regular_read_odd_bytes_with_no_more_config) 
				$display("regular_read_odd_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_read_odd_bytes_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////	

property regular_read_even_bytes_with_no_more_config ;  
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (!(i_regf_DATA_LEN_tb[0]))
	&& (i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_read |-> ##22 sec_stage_data_pre  
	|-> ##78 fourth_stage_crc_pre_r  |-> ##22 (dut.dut0.current_state =='d17) ;
			
	
			
	endproperty:regular_read_even_bytes_with_no_more_config
		
	regular_read_even_bytes_1: assert property (regular_read_even_bytes_with_no_more_config) 
				$display("regular_read_even_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_read_even_bytes_with_no_more_config is FAILED at %0t",$time) ;		

///////////////////////////////////////////////////////////////////////////////////////////////////////////	

property regular_read_odd_bytes_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (i_regf_DATA_LEN_tb[0])
	&& (i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_read |-> ##22 sec_stage_data_pre  |-> ##58  zeros_byte_r 
	|-> ##6 fourth_stage_crc_pre_r  ##22 (dut.dut0.current_state =='d16) ;

			
	
			
	endproperty:regular_read_odd_bytes_with_coming_config
		
	regular_read_odd_bytes_2: assert property (regular_read_odd_bytes_with_coming_config) 
				$display("regular_read_odd_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_read_odd_bytes_with_coming_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////	

property regular_read_even_bytes_with_coming_config ;  
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (!i_regf_cmd_attr_tb) && (!(i_regf_DATA_LEN_tb[0]))
	&& (i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_read |-> ##22 sec_stage_data_pre    
	|-> ##78 fourth_stage_crc_pre_r  |-> ##22 (dut.dut0.current_state =='d16) ;
			
	
			
	endproperty:regular_read_even_bytes_with_coming_config
		
	regular_read_even_bytes_2: assert property (regular_read_even_bytes_with_coming_config) 
				$display("regular_read_even_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("regular_read_even_bytes_with_coming_config is FAILED at %0t",$time) ;	
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_one_byte_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd1)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  |-> ##18  zeros_byte_w 
	|-> ##6 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
			
	endproperty:immidiate_write_one_byte_with_no_more_config
		
	immidiate_write_one_byte_1: assert property (immidiate_write_one_byte_with_no_more_config) 
				$display("immidiate_write_one_byte_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_one_byte_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_one_byte_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd1)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  |-> ##18  zeros_byte_w 
	|-> ##6 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d16) ;
			
	
			
	endproperty:immidiate_write_one_byte_with_coming_config
		
	immidiate_write_one_byte_2: assert property (immidiate_write_one_byte_with_coming_config) 
				$display("immidiate_write_one_byte_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_one_byte_with_coming_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////	

property immidiate_write_two_bytes_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd2)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  /*|-> ##34  zeros_byte_w */
	|-> ##38 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
		
	endproperty:immidiate_write_two_bytes_with_no_more_config
		
	immidiate_write_two_bytes_1: assert property (immidiate_write_two_bytes_with_no_more_config) 
				$display("immidiate_write_two_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_two_bytes_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////


property immidiate_write_two_bytes_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd2)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0)&& (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  /*|-> ##34  zeros_byte_w */
	|-> ##38 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d16) ;
			
	
		
	endproperty:immidiate_write_two_bytes_with_coming_config
		
	immidiate_write_two_bytes_2: assert property (immidiate_write_two_bytes_with_coming_config) 
				$display("immidiate_write_two_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_two_bytes_with_coming_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_three_bytes_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd3)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre /* |-> ##60  zeros_byte_w */
	|-> ##80 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
		
	endproperty:immidiate_write_three_bytes_with_no_more_config
		
	immidiate_write_three_bytes_1: assert property (immidiate_write_three_bytes_with_no_more_config) 
				$display("immidiate_write_three_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_three_bytes_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_three_bytes_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd3)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (!(check_error == 'b1) ) )
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre  |-> ##60  zeros_byte_w 
	|-> ##6 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d16) ;
			
	
		
	endproperty:immidiate_write_three_bytes_with_coming_config
		
	immidiate_write_three_bytes_2: assert property (immidiate_write_three_bytes_with_coming_config) 
				$display("immidiate_write_three_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_three_bytes_with_coming_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_four_bytes_with_no_more_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd4)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (!(check_error == 'b1)))
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre /* |-> ##60  zeros_byte_w */
	|-> ##80 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d17) ;
			
	
		
	endproperty:immidiate_write_four_bytes_with_no_more_config
		
	immidiate_write_four_bytes_1: assert property (immidiate_write_four_bytes_with_no_more_config) 
				$display("immidiate_write_four_bytes_with_no_more_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_four_bytes_with_no_more_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property immidiate_write_four_bytes_with_coming_config ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (!i_regf_toc_tb) && (i_regf_cmd_attr_tb) && (i_regf_dtt_tb == 'd4)
	&& (!i_regf_wr_rd_bit_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (!(check_error == 'b1)))
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##22 sec_stage_data_pre /* |-> ##60  zeros_byte_w */
	|-> ##80 fourth_stage_crc_pre_w |-> ##2 token_crc |-> ##12 (dut.dut0.current_state =='d16) ;
			
	
		
	endproperty:immidiate_write_four_bytes_with_coming_config
		
	immidiate_write_four_bytes_2: assert property (immidiate_write_four_bytes_with_coming_config) 
				$display("immidiate_write_four_bytes_with_coming_config is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("immidiate_write_four_bytes_with_coming_config is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////


property nack_error_r ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (check_error == 'b1) && (nack_error == 'b1)
	&& (i_regf_wr_rd_bit_tb))
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_read |-> ##26 (dut.dut0.current_state =='d15) ;
			
	
		
	endproperty:nack_error_r
		
	error_1: assert property (nack_error_r) 
				$display("nack_error_r is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("nack_error_r is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property nack_error_w ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (check_error == 'b1) && (nack_error == 'b1) 
	&& (!i_regf_wr_rd_bit_tb))
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##26 (dut.dut0.current_state =='d15) ;
			
	
		
	endproperty:nack_error_w
		
	error_2: assert property (nack_error_w) 
				$display("nack_error_w is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("nack_error_w is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////

property aborting ;
	
	@( posedge i_sys_clk_tb) ((i_sys_rst_tb) && (dut.dut0.current_state =='d1) && (dut.dut4.o_cnt_bit_count =='d0) 
	&& (dut.dut3.o_scl_pos_edge ==0) && (dut.dut3.o_scl_neg_edge ==0) && (check_error == 'b1) && (abort_error == 'b1) 
	&& (!i_regf_wr_rd_bit_tb))
	
	|-> o_sdahnd_serial_data_tb |-> ##3 command_word_write |-> ##66 (dut.dut0.current_state =='d15) ;
			
	
		
	endproperty:aborting
		
	error_3: assert property (aborting) 
				$display("aborting is SUCCEEDED at %0t",$time); 
		 else 		
				$info ("aborting is FAILED at %0t",$time) ;
				
///////////////////////////////////////////////////////////////////////////////////////////////////////////
				
				
				
//--------------------------------------Sequences----------------------------------//	
	sequence command_word_write ;
			(!o_sdahnd_serial_data_tb)  ##2 (o_sdahnd_serial_data_tb)  ##2 zeros_byte_w   ;   // first 10 bits 
	endsequence : command_word_write
	                                                 
	
	sequence command_word_read ;
			(!o_sdahnd_serial_data_tb)  ##2 (o_sdahnd_serial_data_tb)  ##2 o_sdahnd_serial_data_tb
			 ##2 seven_zeros_w   ;   // first 10 bits 
	endsequence : command_word_read
	
	
	
	
	sequence zeros_byte_w ;
			(!o_sdahnd_serial_data_tb) [*15]   ;
	endsequence : zeros_byte_w
	
	
	sequence zeros_byte_r ;
			(!i_sdahnd_rx_sda_tb) [*15]   ;
	endsequence : zeros_byte_r
	
	sequence seven_zeros_w ;
			(!o_sdahnd_serial_data_tb) [*13]   ;
	endsequence : seven_zeros_w
	
	
	sequence sec_stage_data_pre ;
			(o_sdahnd_serial_data_tb)[*3]   ;
	endsequence : sec_stage_data_pre
	
	sequence fourth_stage_crc_pre_w ;
			(!o_sdahnd_serial_data_tb)
		##2 (o_sdahnd_serial_data_tb) ;
	endsequence : fourth_stage_crc_pre_w
	
	sequence fourth_stage_crc_pre_r ;
			(!i_sdahnd_rx_sda_tb)
		##2 (i_sdahnd_rx_sda_tb) ;
	endsequence : fourth_stage_crc_pre_r
	
	
	sequence token_crc ;
			(o_sdahnd_serial_data_tb)
		##2 (o_sdahnd_serial_data_tb)
		##2 (!o_sdahnd_serial_data_tb)
		##2 (!o_sdahnd_serial_data_tb);
	endsequence : token_crc
	
	
	
			
				
			
	
		
	
	
//--------------------------------------TASKS----------------------------------//	
	task passing_inputs ;
				
                	 i_engine_en_tb 			 = nt.i_engine_en_tb;
                	 i_regf_toc_tb 				 = nt.i_regf_toc_tb;
					 i_regf_dev_index_tb 		 = nt.i_regf_dev_index_tb;
                     i_regf_short_read_tb   	 = nt.i_regf_short_read_tb;
					 i_regf_wroc_tb		   		 = nt.i_regf_wroc_tb;
					 i_regf_wr_rd_bit_tb  	     = nt.i_regf_wr_rd_bit_tb;
                     i_regf_cmd_attr_tb    	     = nt.i_regf_cmd_attr_tb;
					 i_regf_dtt_tb               = nt.i_regf_dtt_tb;
					 i_regf_tx_parallel_data_tb  = nt.i_regf_tx_parallel_data_tb;
					 i_crc_crc_value_tb          = nt.i_crc_crc_value_tb;
					 i_sdahnd_rx_sda_tb          = nt.i_sdahnd_rx_sda_tb;
					 i_crc_valid_tb              = nt.i_crc_valid_tb;
					 i_sdr_ctrl_scl_idle_tb      = nt.i_sdr_ctrl_scl_idle_tb;
					 i_timer_cas_tb              = nt.i_timer_cas_tb;
					 i_ccc_Direct_Broadcast_n_tb = nt.i_ccc_Direct_Broadcast_n_tb;
					 i_regf_DATA_LEN_tb          = nt.i_regf_DATA_LEN_tb;
					 
					 check_error                 = nt.check_error;
					 nack_error                	 = nt.nack_error;
					 abort_error                 = nt.abort_error;
					 
					 
	endtask
	
	
	
	task rsest ;
		
		@ (negedge i_sys_clk_tb);
		i_sys_rst_tb = 0 ;
		
		#(5*CLK_PERIOD);
		
		i_sys_rst_tb = 1 ;
		
		#(CLK_PERIOD);
		
		
		
	endtask
	
	
	task initialize ;
		i_sys_clk_tb = 0 ;
		i_sys_rst_tb = 1;
	endtask
	
	


	
 /*always@(*) begin
    case (i_regf_dev_index_tb)                     
        5'd0 : dev_address	   =     7'd8  ;   
        5'd1 : dev_address     =     7'd9  ;  //0001001
        5'd2 : dev_address     =     7'd10 ;
        5'd3 : dev_address     =     7'd11 ;

        5'd4 : dev_address     =     7'd12 ;
        5'd5 : dev_address     =     7'd13 ;
        5'd6 : dev_address     =     7'd14 ;
        5'd7 : dev_address     =     7'd15 ;

        5'd8 : dev_address     =     7'd16 ; //0010000
        5'd9 : dev_address     =     7'd17 ;
        5'd10: dev_address     =     7'd18 ;
        5'd11: dev_address     =     7'd19 ;

        5'd12: dev_address     =     7'd20 ;
        5'd13: dev_address     =     7'd21 ;
        5'd14: dev_address     =     7'd22 ;
        5'd15: dev_address     =     7'd23 ;

        5'd16: dev_address 	   = 	 7'd24 ;
        5'd17: dev_address	   = 	 7'd25 ;
        5'd18: dev_address 	   = 	 7'd26 ;
        5'd19: dev_address	   = 	 7'd27 ;

        5'd20: dev_address	   = 	 7'd28 ;
        5'd21: dev_address	   = 	 7'd29 ;
        5'd22: dev_address	   =  	 7'd30 ;
        5'd23: dev_address     = 	 7'd31 ;

        5'd24: dev_address 	   =	 7'd32 ;
        5'd25: dev_address	   = 	 7'd33 ;
        5'd26: dev_address 	   = 	 7'd34 ;
        5'd27: dev_address	   = 	 7'd35 ;

        5'd28: dev_address     = 	 7'd36 ;
        5'd29: dev_address     = 	 7'd37 ;
        5'd30: dev_address     = 	 7'd38 ;
        5'd31: dev_address     = 	 7'd39 ;
    endcase

end */

always @(*)
	begin 
	
		if (i_regf_DATA_LEN_tb[0])
			data_delay = ( (5*16) +  ((5-1)*4) ) + 2 ;  //8  //8 8 2 2 8  // 8 8 2 2 8 8 2 2 8 // 8 8 2 2 8 8 2 2 8 8 2 2 8
	
		//2 16 16 4 4 16 

	
	end



endmodule
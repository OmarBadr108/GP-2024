module tx_tb ();

reg        i_sys_clk_tb;
reg        i_sys_rst_tb;
reg        i_ddrccc_tx_en_tb;
wire       scl_pos_edge_tb;
wire       scl_neg_edge_tb;
reg [3:0]  i_ddrccc_tx_mode_tb;
reg [7:0]  i_regf_tx_parallel_data_tb;
reg [7:0]  i_ddrccc_special_data_tb; // special from ddr or ccc   
reg [4:0]  i_crc_crc_value_tb;


wire         o_sdahnd_serial_data_tb;
wire         o_ddrccc_mode_done_tb;
wire  [7:0]  o_crc_parallel_data_tb;
wire         o_ddrccc_parity_data_tb;
wire         o_crc_en_tb;


reg 	   i_scl_gen_stall_tb , i_sdr_ctrl_scl_idle_tb , i_timer_cas_tb , i_sdr_scl_gen_pp_od_tb ;
wire 	  o_scl_tb ;

// tx modes needed 
localparam [3:0]  special_preambles = 'b0000, //2'b01 
                  serializing_address = 'b0001, //address of target
    				          serializing_zeros = 'b0011 ,  //7-zeros in the first byte of cmd word        
                  one = 'b0010, // for representing preamble bit or reading_or_writing bit  
                  zero = 'b0110, // for representing preamble bit or reading_or_writing bit
				          serializing_data = 'b0111, //data byte from reg to be serialized
				          CCC_value = 'b0101 , //special data in case of transmitting CCC
				          calculating_Parity = 'b0100, //parity of word serialized either cmd word or data word
				          token_CRC = 'b1100, //special bits 4'b1100
				          CRC_value = 'b1101, //CRC value arrived of data serialized
                  restart_Pattern = 'b1111,
                  exit_Pattern = 'b1110;
	
parameter CLK_PERIOD = 20;
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb ;


scl_generation DUT0 (
		.i_sdr_ctrl_clk      (i_sys_clk_tb),
		.i_sdr_ctrl_rst_n 	 (i_sys_rst_tb),
		.i_sdr_scl_gen_pp_od (i_sdr_scl_gen_pp_od_tb),
		.i_scl_gen_stall  	 (i_scl_gen_stall_tb),
		.i_sdr_ctrl_scl_idle (i_sdr_ctrl_scl_idle_tb),
		.i_timer_cas         (i_timer_cas_tb),
		.o_scl_pos_edge      (scl_pos_edge_tb),
		.o_scl_neg_edge      (scl_neg_edge_tb),
		.o_scl 	 			         (o_scl_tb)
 );
 
	
tx DUT1 (
.i_sys_clk (i_sys_clk_tb),
.i_sys_rst (i_sys_rst_tb),
.i_ddrccc_tx_en (i_ddrccc_tx_en_tb),
.i_sclgen_scl_pos_edge (scl_pos_edge_tb),
.i_sclgen_scl_neg_edge (scl_neg_edge_tb),
.i_ddrccc_tx_mode (i_ddrccc_tx_mode_tb),
.i_regf_tx_parallel_data (i_regf_tx_parallel_data_tb),
.i_ddrccc_special_data (i_ddrccc_special_data_tb),
.i_crc_crc_value (i_crc_crc_value_tb),
.o_sdahnd_serial_data (o_sdahnd_serial_data_tb),
.o_ddrccc_mode_done (o_ddrccc_mode_done_tb),
.o_crc_parallel_data (o_crc_parallel_data_tb),
.o_crc_en (o_crc_en_tb),
.o_ddrccc_parity_data (o_ddrccc_parity_data_tb)
);


initial 
 begin
   
    i_sys_clk_tb = 0;
		i_sys_rst_tb    = 1'b1 ; // not asserted 
		i_scl_gen_stall_tb     = 1'b0 ;
		i_sdr_scl_gen_pp_od_tb = 1;
		i_sdr_ctrl_scl_idle_tb = 1'b0 ;
		i_timer_cas_tb 	 	   = 1'b0 ;
		
		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b0 ; // asserted

		#(3*CLK_PERIOD);
		i_sys_rst_tb    = 1'b1 ; // not asserted
		
		#(7*CLK_PERIOD);
		
		
		i_ddrccc_tx_en_tb = 1;
		i_ddrccc_tx_mode_tb = special_preambles; //start with special pereamble
		@(posedge o_ddrccc_mode_done_tb); //wait until mode done
		#(CLK_PERIOD); //wait a sys clk cycle for recieving the new mode
		
		
		i_ddrccc_tx_mode_tb = zero; //mode of sending zero representing the write bit in the cmd word
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = serializing_zeros; //mode of sending seven zeros to complete the first byte of cmd word
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_special_data_tb = 8'b01100110; //i will use in this mode just the first 7 bits that represent address
		i_ddrccc_tx_mode_tb = serializing_address; //mode of sending the address and the parity adj (second byte of cmd word)
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = calculating_Parity; //mode of sending the parity of the cmd word
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = one; //mode of sending one representing the first preamble of the second stage of preambles
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_en_tb = 0; //disable tx for enabling rx to recieve ack bit 
		#(2*CLK_PERIOD);
		
		
		i_ddrccc_special_data_tb = 8'b10101010; //use here the special data came from level 2 as ccc_value in data word
		i_ddrccc_tx_en_tb = 1;
		i_ddrccc_tx_mode_tb = CCC_value; //mode of sending ccc_value as first byte of data word
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_regf_tx_parallel_data_tb = 8'b11001001; 
	  i_ddrccc_tx_mode_tb = serializing_data; //mode of sending data byte as second byte of data word
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = calculating_Parity; //mode of sending the parity of the data word (same mode of cmd word parity by using internal flag)
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		

		i_ddrccc_tx_mode_tb = special_preambles; //sending special preamble 'b10 indicating end of transmission and crc in the waaay
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = token_CRC; //mode of sending crc token 'b1100
		#(3*CLK_PERIOD); 
		i_crc_crc_value_tb = 'b10110; //the crc values arrived from crc block
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_mode_tb = CRC_value; //sending crc values
		@(posedge o_ddrccc_mode_done_tb);
		#(CLK_PERIOD);
		
		
		i_ddrccc_tx_en_tb = 0;
		#(4*CLK_PERIOD);
		$stop ;

		$stop;

		

 end
 
 endmodule
		
		
		
		
		
		
		
		
   
	





 module Exit_Detector_TB ();
 
 reg          i_sys_clk_tb;
 reg          i_sys_rst_tb;
 reg          i_cccnt_enable_tb;
 reg          i_scl_tb;
 reg          i_sda_tb;

 wire         o_cccnt_done_tb;
 
Exit_Detector dut (
    .i_sys_clk(i_sys_clk_tb),
    .i_sys_rst(i_sys_rst_tb),
    .i_cccnt_enable(i_cccnt_enable_tb),
    .i_scl(i_scl_tb),
    .i_sda(i_sda_tb),
    .o_cccnt_done(o_cccnt_done_tb)
);


// Clock generation
parameter CLK_PERIOD =10;
always #(CLK_PERIOD/2) i_sys_clk_tb = ~i_sys_clk_tb; 


initial 
	begin 
		i_sys_clk_tb ='b0;
		i_sys_rst_tb ='b1;
		
		@(negedge i_sys_clk_tb);
		i_sys_rst_tb ='b0;
		
		@(posedge i_sys_clk_tb);
		@(posedge i_sys_clk_tb);	
		i_sys_rst_tb ='b1;
		i_scl_tb = 'b0;
		i_sda_tb = 'b1;
		i_cccnt_enable_tb ='b1;
		
		repeat (7) begin 
		#(2*CLK_PERIOD);
		i_sda_tb = ~ i_sda_tb;
		end 
		/*#(2*CLK_PERIOD);
		i_sda_tb = 'b0;
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b1;
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b0;
		
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b1;
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b0;
		
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b1;
		
		
		#(2*CLK_PERIOD);
		i_sda_tb = 'b0;*/
		
		#(CLK_PERIOD);
		i_scl_tb = 'b1;
		
		#(CLK_PERIOD);
		$stop;
		
	end
	
	
	
	endmodule 
		
		
		
		
		
		
		
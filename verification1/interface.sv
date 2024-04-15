interface bus_if(input logic  i_sdr_clk,i_sdr_rst_n);
	
	//in

    logic          i_controller_en                ;
    logic          i_i3c_i2c_sel                  ;
    logic          i_ccc_en_dis_hj                ;
    

    logic  [7:0]   i_regf_config            ;
    logic          i_data_config_mux_sel	  ;  

    logic  [11:0]  i_regf_wr_address_config ;
    logic          i_regf_wr_en_config      ;
    logic          i_regf_rd_en_config      ;


    
    logic          i_hdr_en                 ; 
    logic          i_ccc_done               ;
    logic          i_ddr_mode_done          ;
     

    //inout
    logic          sda                      ; 
    
    //out
    logic          o_ddrmode_enable         ;
    logic          o_ccc_enable             ;
    logic   [11:0]  o_regf_address_special  ;
    logic          scl                      ; 
    logic          o_sdr_rx_valid           ; 
    logic          o_ctrl_done              ;


modport DUT (input i_controller_en, 
                    i_i3c_i2c_sel,   
                    i_ccc_en_dis_hj,
                    i_regf_config  ,         
					i_data_config_mux_sel,	
                    i_regf_wr_address_config,
                    i_regf_wr_en_config  ,   
                    i_regf_rd_en_config  ,  
                    i_hdr_en             ,    
                    i_ccc_done           ,   
                    i_ddr_mode_done      ,   
               
             
             inout  sda                  , 
             
             output o_ddrmode_enable     ,   
                    o_ccc_enable         ,   
                    o_regf_address_special, 
                    scl,                     
                    o_sdr_rx_valid,          
                    o_ctrl_done            );


modport TB (output i_controller_en, 
                    i_i3c_i2c_sel,   
                    i_ccc_en_dis_hj,
                    i_regf_config  ,         
					i_data_config_mux_sel,	
                    i_regf_wr_address_config,
                    i_regf_wr_en_config  ,   
                    i_regf_rd_en_config  ,  
                    i_hdr_en             ,    
                    i_ccc_done           ,  
                    i_ddr_mode_done      ,   
                
             
             inout  sda                  , 
             
             input  o_ddrmode_enable     ,   
                    o_ccc_enable         ,   
                    o_regf_address_special, 
                    scl,                     
                    o_sdr_rx_valid,          
                    o_ctrl_done            );


endinterface : bus_if
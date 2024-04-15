

class transaction ;
// declaring inputs whose values will be randomized

 rand bit               i_controller_en  			;               
 rand bit               i_i3c_i2c_sel     			;  
 //rand bit     [7:0]  	i_regf_config      			;         
 rand bit               i_data_config_mux_sel       ;                    
 rand bit               i_regf_wr_en_config         ;   
 rand bit               i_regf_rd_en_config         ;    
 rand bit               i_hdr_en            		;
 rand bit               i_ccc_done          		;
 rand bit               i_ddr_mode_done     		;


 //rand bit     [7:0]  	i_regf_config      			;
rand bit    [2:0]   CMD_ATTR 						;
rand bit	[3:0]	TID 							;
rand bit	[7:0]	CMD 							;
rand bit			CP 								; 
rand bit	[4:0]   DEV_INDEX  						;
rand bit	[1:0]   RESERVED   					    ;
rand bit	[2:0]   DTT        						;			
rand bit	[2:0]   MODE 	 						;
rand bit			TOC  	  						;
rand bit			WROC 							;
rand bit			RnW 							;
rand bit	[7:0]	DEF_BYTE 						;
rand bit	[7:0]	DATA_TWO 						;
rand bit	[7:0]   DATA_THREE 						; 
rand bit	[7:0]   DATA_FOUR  						;  


// adding constraints for the randomized values
constraint controller_en_rand 		    { 

	i_controller_en inside {0,1};
}
constraint i3c_i2c_sel_rand   		    { 

	i_i3c_i2c_sel inside {0,1};
}
constraint data_config_mux_sel_rand     { 

	i_data_config_mux_sel inside {0,1};
}

constraint regf_wr_en_config_rand     	{

	i_regf_wr_en_config  inside {0,1};
}
constraint regf_rd_en_config_rand   	{ 

	i_regf_rd_en_config inside {0,1};
}
constraint hdr_en_rand  			    { 

	i_hdr_en inside {0,1};
}
constraint ccc_done_rand                {

 	i_ccc_done inside {0,1};
}
constraint ddr_mode_done_rand           {

    i_ddr_mode_done inside {0,1};
}

	constraint CMD_ATTR {
		CMD_ATTR dist {1:/70 , 0:/30} ;	
	}

	constraint TID {
		TID inside {[0:15]} ;	
	}

	constraint CMD {
		CMD inside {[0:1],['h80:'h81],['h89:'h8a],['h8b:'h8c],['h09:'h0a],'h9a ,'h2a ,'h90} ;	
	}
	
	constraint CP {
		CP inside {[0:1]} ;	
	}

	constraint DEV_INDEX {
		DEV_INDEX inside {[0:31]} ;	
	}

	constraint RESERVED {
		RESERVED inside {[0:3]} ;	
	}

	constraint DTT {
		DTT inside {[0:7]} ;	
	}

	constraint MODE {
		MODE == 6 ;	
	}

	constraint RnW {
		RnW inside {[0:1]} ;	
	}

	constraint WROC {
		WROC inside {[0:1]} ;	
	}

	constraint TOC {
		TOC inside {[0:1]} ;	
	}


	constraint DEF_BYTE {
		DEF_BYTE inside {[0:255]} ;	
	}

	constraint DATA_TWO {
		DATA_TWO inside {[0:255]} ;	
	}

	constraint DATA_THREE {
		DATA_THREE inside {[0:255]} ;	
	}

	constraint DATA_FOUR {
		DATA_FOUR == 0 ;	
	}
	

endclass 



task write_configurations;
	begin
		transaction tr = new()
// DWORD 0
repeat(10) begin
	tr.randomize();
	
	 #(2*CLK_PERIOD)																		    			; 
		i_regf_config    = { CMD[0] , TID , CMD_ATTR }  												    ;
    	i_regf_wr_address_config = config_location 															;
    	    
      #(2*CLK_PERIOD)  																		; 
		i_regf_config    = { CP , CMD[7:1] } 															    ;
    	i_regf_wr_address_config = config_location + 'd1 														;

      #(2*CLK_PERIOD)  																		; 
		i_regf_config    = { DTT[0] , RESERVED , DEV_INDEX }  											    ;		    
    	i_regf_wr_address_config = config_location + 'd2 														;

      #(2*CLK_PERIOD)  																		; 
		i_regf_config    = { TOC , WROC , RnW , MODE , DTT[2:1]} 										;
    	i_regf_wr_address_config = config_location + 'd3 														;

  // DWORD 1
       #(2*CLK_PERIOD) ;  																		; 
		i_regf_config    = DEF_BYTE     																;
    	i_regf_wr_address_config = config_location + 'd4 														;	

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config    = DATA_TWO     																;
    	i_regf_wr_address_config = config_location + 'd5 														;

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config    = DATA_THREE     																;
    	i_regf_wr_address_config = config_location + 'd6 														;

       #(2*CLK_PERIOD) ; 																		; 
		i_regf_config    = DATA_FOUR     																;
    	i_regf_wr_address_config = config_location + 'd7 														;


  
        #(CLK_PERIOD) ;
     end
	end
endtask

endclass
package CCC_HANDLER_PACKAGE ;
	parameter CLK_PERIOD        = 20 ; 
	parameter configuration_mux = 1'b1 ;
    parameter Design_mux  	 	= 1'b0 ;
    parameter config_location   = 12'd1000 ;
    parameter special_config    = 12'd450 ;


class configuration ;
	// DWORD0
	rand bit  [2:0] RAND_CMD_ATTR ;
	rand bit  [3:0] RAND_TID ;
	rand bit  [7:0] RAND_CMD ;
	rand bit  		 RAND_CP ;
	rand bit  [4:0] RAND_DEV_INDEX ;
	rand bit  [1:0] RAND_RESERVED ;
	rand bit  [2:0] RAND_DTT ;
	rand bit  [2:0] RAND_MODE ;
	rand bit 		 RAND_RnW ;
	rand bit  		 RAND_WROC ;
	rand bit  		 RAND_TOC ;

	// DWORD1
	rand bit  [7:0] RAND_DEF_BYTE ;
	rand bit  [7:0] RAND_DATA_TWO ;
	rand bit  [7:0] RAND_DATA_THREE ;
	rand bit  [7:0] RAND_DATA_FOUR ;

	constraint CMD_ATTR {
		RAND_CMD_ATTR dist {1:/70 , 0:/30} ;	
	}

	constraint TID {
		RAND_TID inside {[0:15]} ;	
	}

	constraint CMD {
		RAND_CMD inside {[0:1],['h80:'h81],['h89:'h8a],['h8b:'h8c],['h09:'h0a],'h9a ,'h2a ,'h90} ;	
	}
	
	constraint CP {
		RAND_CP inside {[0:1]} ;	
	}

	constraint DEV_INDEX {
		RAND_DEV_INDEX inside {[0:31]} ;	
	}

	constraint RESERVED {
		RAND_RESERVED inside {[0:3]} ;	
	}

	constraint DTT {
		RAND_DTT inside {[0:7]} ;	
	}

	constraint MODE {
		RAND_MODE == 6 ;	
	}

	constraint RnW {
		RAND_RnW inside {[0:1]} ;	
	}

	constraint WROC {
		RAND_WROC inside {[0:1]} ;	
	}

	constraint TOC {
		RAND_TOC inside {[0:1]} ;	
	}


	constraint DEF_BYTE {
		RAND_DEF_BYTE inside {[0:255]} ;	
	}

	constraint DATA_TWO {
		RAND_DATA_TWO inside {[0:255]} ;	
	}

	constraint DATA_THREE {
		RAND_DATA_THREE inside {[0:255]} ;	
	}

	constraint DATA_FOUR {
		RAND_DATA_FOUR inside {[0:255]} ;	
	}
	

endclass 
endpackage : CCC_HANDLER_PACKAGE
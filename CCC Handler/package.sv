package CCC_HANDLER_PACKAGE ;
    parameter CLK_PERIOD        = 20 ; 
    parameter REGF_CLK_PERIOD   = 10 ;
	parameter configuration_mux = 1'b1 ;
    parameter Design_mux  	    = 1'b0 ;
    parameter config_location   = 12'd1000 ;
    parameter special_config    = 12'd450 ;


// CCC Handler states
parameter  [4:0]   IDLE               = 5'd0  , // 0
                   PRE_CMD            = 5'd1  , // 1
                   RNW                = 5'd2  , // 2
                   RESERVED           = 5'd3  , // 3
                   SECOND_CMD_BYTE    = 5'd4  , // 4
                   PARITY_CMD         = 5'd5  , 
                   PRE_FIRST_DATA_ONE = 5'd6  , 
                   PRE_FIRST_DATA_TWO = 5'd7  , 
                   CCC_BYTE           = 5'd8  , 
                   DEFINING_BYTE      = 5'd9  , 
                   ZEROS              = 5'd10 ,
                   PARITY_DATA        = 5'd11 ,
                   PRE_DATA_ONE       = 5'd12 ,
                   PRE_DATA_TWO       = 5'd13 , 
                   FIRST_DATA_BYTE    = 5'd14 , 
                   SECOND_DATA_BYTE   = 5'd15 ,
                   C_TOKEN_STATE      = 5'd16 , 
                   CRC_CHECKSUM_STATE = 5'd17 , 
                   RESTART_PATTERN    = 5'd18 , 
                   EXIT_PATTERN       = 5'd19 , 
                   ERROR              = 5'd20 , 
                   FINISH             = 5'd21 , 
                   PRE_CRC_TARGET     = 5'd22 ,
                   RESTART_PATTERN_SPECIAL = 5'd23 ;


    // tx modes parameters 
parameter [3:0]  
                zero                   = 4'd6  ,  //                        
                one                    = 4'd2  ,  //                        
                special_preamble       = 4'd0  ,  // 01 of cmd word          
                seven_zeros            = 4'd3  ,  // 7'b 0000_000            
                serializing_address    = 4'd1  ,  // serializing 7 bits + 1 bit ParAdj      
                serializing_byte_port  = 4'd5  ,  // serializing 8 bits that given from CCC to tx not from regfile to tx 
                serializing_byte_regf  = 4'd7  ,  //                         
                parity_calc            = 4'd4  ,  //                        
                c_token_CRC            = 4'd12 ,  // 4'hC                    
                value_CRC              = 4'd13 ,  // 5 bit value             
                restart_pattern        = 4'd15 ,  //                         
                exit_pattern           = 4'd14 ;  // 

// regfile parameters 
parameter [11:0] first_location = 12'd1000 ;


// rx parameters 
parameter [2:0] 
                 preamble_rx_mode    = 3'd0 , 
                 CRC_PREAMBLE        = 3'd1 ,
                 parity_check        = 3'd6 ,
                 deserializing_byte  = 3'd3 ,
                 check_c_token_CRC   = 3'd7 ,
                 check_value_CRC     = 3'd2 ;
  
// SCL staller parameters 
parameter [4:0] restart_pattern_stall = 5'd7, 
                restart_pattern_stall_special = 5'd7, 
                exit_pattern_stall    = 5'd13 ;  


// Error states parameters 
localparam [3:0] 
                SUCCESS     = 4'h0  ,
                CRC_ERR     = 4'h1  ,
                PARITY_ERR  = 4'h2  ,
                FRAME       = 4'h3  ,
                ADDR_HEADER = 4'h4  ,
                NACK        = 4'h5  ,
                OVL         = 4'h6  ,
                SRE         = 4'h7  ,
                C_ABORTED   = 4'h8  ,
                T_ABORTED   = 4'h9  ;


parameter [6:0] SEVEN_E = 7'h7E ;

// CCC values 
parameter [7:0] 
        ENEC_D      = 8'h80 ,   
        DISEC_D     = 8'h81 , 
        SETMWL_D    = 8'h89 ,
        SETMRL_D    = 8'h8A ,
        GETMWL_D    = 8'h8B ,
        GETMRL_D    = 8'h8C ,
        GETSTATUS_D = 8'h90 ,
        GETPID_D    = 8'h8D ,
        GETBCR_D    = 8'h8E ,
        GETDCR_D    = 8'h8F ,
        ENEC_B      = 8'h00 ,
        DISEC_B     = 8'h01 ,
        SETMWL_B    = 8'h09 ,
        SETMRL_B    = 8'h0A ,
        Dummy_B 	= 8'h1F ;

class configuration ;
	// DWORD0
	rand bit  [2:0] RAND_CMD_ATTR     ;
	rand bit  [3:0] RAND_TID          ;
	rand bit  [7:0] RAND_CMD          ;
	rand bit        RAND_CP           ;
	rand bit  [4:0] RAND_DEV_INDEX    ;
	rand bit  [1:0] RAND_RESERVED     ;
	rand bit  [2:0] RAND_DTT          ;
	rand bit  [2:0] RAND_MODE         ;
	rand bit        RAND_RnW          ;
	rand bit        RAND_WROC         ;
	rand bit        RAND_TOC          ;

	// DWORD1
	rand bit  [7:0] RAND_DEF_BYTE     ;
	rand bit  [7:0] RAND_DATA_TWO     ;
	rand bit  [7:0] RAND_DATA_THREE   ;
	rand bit  [7:0] RAND_DATA_FOUR    ;    
    //rand bit 		RAND_SDA ; 			
   
 
	constraint CMD_ATTR {
		//RAND_CMD_ATTR inside { 0 , 1 } ;
		RAND_CMD_ATTR dist {1:/70 , 0:/30} ;
	}
	
	constraint TID {
		RAND_TID inside {[0:15]} ;	
	}

	constraint CMD {
		RAND_CMD inside {8'h00 , 8'h01 , 8'h09 , 8'h0A , 8'h1F	 	 	 // broadcast 
					    ,8'h80 , 8'h81 , 8'h89 , 8'h8A  				 // direct set
					    ,8'h8B , 8'h8C , 8'h90 , 8'h8E , 8'h8F  	 	 // direct get
					    //,8'h8D	 	  		 		 	 	 	 	 // GETPID	 
						 								   		} ;	
	}

	constraint CP {
		RAND_CP == 1  ;	
	}

	constraint DEV_INDEX {
		RAND_DEV_INDEX inside {[1:31]} ;	
	}

	constraint RESERVED {
		RAND_RESERVED inside {[0:3]} ;	
	}

	constraint DTT {
		RAND_DTT inside {0,1,2} ;	
	}

	constraint MODE {
		RAND_MODE == 6 ;	
	}

	constraint RnW {
		RAND_RnW == ((RAND_CMD == 8'h00)|(RAND_CMD == 8'h01)|(RAND_CMD == 8'h09)|(RAND_CMD ==8'h0A)|
					 (RAND_CMD == 8'h80)|(RAND_CMD == 8'h81)|(RAND_CMD == 8'h89)|(RAND_CMD ==8'h8A)|(RAND_CMD ==8'h1F))? 0 : 1 ;	
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

	constraint DATA_LENGTH {
		RAND_DATA_THREE inside {1,2} ;	
	}

	constraint DATA_FOUR {
		RAND_DATA_FOUR == 0 ;	
	}
	
endclass 
endpackage : CCC_HANDLER_PACKAGE
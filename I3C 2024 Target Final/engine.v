module Target_engine (
	input wire 		 i_sys_clk ,
	input wire 		 i_sys_rst ,
	input wire 		 i_rstdet_RESTART , 
	input wire 		 i_exitdet_EXIT ,
	input wire 		 i_ENTHDR_done ,
	input wire  	 i_CCC_done ,
	input wire 		 i_NT_done ,
	input wire [1:0] i_rx_decision ,
	input wire 		 i_rx_decision_done ,

	output reg [1:0] o_muxes ,
	output reg 		 o_ENTHDR_en   ,
	output reg 		 o_NT_en     ,
	output reg 	     o_CCC_en    ,
	output reg 	 	 o_rx_en     ,
	output reg [3:0] o_rx_mode     
);


// internal signals 
reg [4:0] current_state , next_state ;

localparam  [4:0]  IDLE_SDR         = 5'd0  ,
                   IDLE_HDR  	    = 5'd1  ,
                   INITIALIZE       = 5'd2  , 
                   CCC_HANDLER      = 5'd3  , 
                   DDR_NT           = 5'd4  ;

////////////////////////////////////////// RX Parameters ////////////////////////////////////////////////

parameter  [3:0]  initializing 			  = 4'b0000,  
                  pereamble 			  = 4'b0001, 
				  deserializing_data 	  = 4'b0010, 
				  deserializing_ccc_value = 4'b0011, 
				  check_Parity 			  = 4'b0100, 
				  token_CRC 			  = 4'b0101, 
				  CRC_value           	  = 4'b0110, 
				  deserializing_address   = 4'b0111, 
				  deserializing_zeros     = 4'b1000, 
				  special_pereamble       = 4'b1001; 

////////////////////////////////////////// decision Parameters //////////////////////////////////////////

parameter  [1:0]  not_me = 2'b00, 
                  me_ddr = 2'b01, 
				  CCC 	 = 2'b10, 
				  error  = 2'b11;

//////////////////////////////////////////// muxes Parameters ///////////////////////////////////////////

parameter  [1:0]  engine = 2'b00, 
                  ddr_nt = 2'b01, 
				  ccc 	 = 2'b10; 
				  			  
////////////////////////////////////////// state memory ////////////////////////////////////////////////

    always @(posedge i_sys_clk or negedge i_sys_rst) begin
        if (!i_sys_rst) begin
            current_state <= IDLE_SDR ;
        end
        else  begin
            current_state <= next_state ;
        end
    end

////////////////////////////////////////// output logic ////////////////////////////////////////////////
 	always @(*) begin
 		case (current_state)
 			IDLE_SDR: begin 
 				o_ENTHDR_en = 1'b1 ;
				o_NT_en     = 1'b0 ;
				o_CCC_en    = 1'b0 ;
				o_rx_en     = 1'b0 ;
				o_rx_mode   = initializing; // no meaining to drive this output here but preventing latching
				o_muxes     = engine ;

				if(i_ENTHDR_done) begin 
					next_state = INITIALIZE ;
				end

				else begin 
					next_state = IDLE_SDR ;
				end 
 			end

 			IDLE_HDR: begin 
 				o_ENTHDR_en = 1'b0 ;
				o_NT_en     = 1'b0 ;
				o_CCC_en    = 1'b0 ;
				o_rx_en     = 1'b0 ;
				o_rx_mode   = initializing; // no meaining to drive this output here but preventing latching 
				o_muxes     = engine ;

				if(i_exitdet_EXIT) begin 
					next_state = IDLE_SDR ;
				end 
				else if (i_rstdet_RESTART) begin 
					next_state = INITIALIZE ;
				end
				else begin 
					next_state = IDLE_HDR ;
				end 
 			end

 			INITIALIZE: begin 
 				o_ENTHDR_en = 1'b0 ;
				o_NT_en     = 1'b0 ;
				o_CCC_en    = 1'b0 ;
				o_rx_en     = 1'b1 ;
				o_rx_mode   = initializing;
				o_muxes     = engine ;

				if(i_rx_decision_done) begin 
					case (i_rx_decision) 
						not_me : begin 
							next_state = IDLE_HDR ;
						end
						error  : begin
							next_state = IDLE_HDR ;
						end  
						me_ddr : begin
							next_state = DDR_NT ;
							o_muxes    = ddr_nt ;
						end 
						CCC    : begin
							next_state = CCC_HANDLER ;
							o_muxes    = ccc ;
						end 
					endcase
				end 
				
				else begin 
					next_state = INITIALIZE ;
				end 
 			end

 			DDR_NT: begin 
 				o_ENTHDR_en = 1'b0 ;
 				o_CCC_en    = 1'b0 ;
				o_NT_en     = 1'b1 ;
				o_muxes     = ddr_nt ;
				o_rx_en     = 1'b0 ;
				o_rx_mode   = initializing; // no meaining to drive this output here but preventing latching

				if(i_NT_done) begin 
					next_state = IDLE_HDR ;
				end 
				
				else begin 
					next_state = DDR_NT ;
				end 
 			end

 			CCC_HANDLER: begin 
 				o_ENTHDR_en = 1'b0 ;
 				o_CCC_en    = 1'b1 ;
				o_NT_en     = 1'b0 ;
				o_muxes     = ccc ;
				o_rx_en     = 1'b0 ;
				o_rx_mode   = initializing; // no meaining to drive this output here but preventing latching
				
				if(i_CCC_done) begin 
					next_state = IDLE_HDR ;
				end 
				
				else begin 
					next_state = CCC_HANDLER ;
				end 
 			end
 		endcase
 	end  
endmodule 
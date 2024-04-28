module target_rx (
  
input                     i_sys_clk,
input                     i_sys_rst,
input                     i_sclgen_scl,
input                     i_sclgen_scl_pos_edge,
input                     i_sclgen_scl_neg_edge,
input                     i_ddrccc_rx_en,
input                     i_sdahnd_rx_sda,
input     [3:0]           i_ddrccc_rx_mode,
input     [4:0]           i_crc_value,

output                    o_ddrccc_rnw,
output  reg  [7:0]        o_regfcrc_rx_data_out,
output  reg               o_ddrccc_rx_mode_done,
output  reg               o_ddrccc_pre,
output  reg  [1:0]        o_engine_decision,
output  reg               o_ddrccc_error_flag,
output  reg  [7:0]        o_ccc_ccc_value

);

localparam [3:0]  initializing = 'b0000,   //done 
                  pereamble = 'b0001, //done
				          deserializing_data = 'b0010, //done
				          deserializing_ccc_value = 'b0011, //done
				          check_Parity = 'b0100, //done
				          token_CRC = 'b0101, //done
				          CRC_value = 'b0110, //done
				          deserializing_address = 'b0111, //done
				          deserializing_zeros = 'b1000, //done
				          special_pereamble = 'b1001; //done
				          				         			          
wire [1:0] special_preamble = 'b01 ;
wire [3:0] token = 4'b1100;
wire [6:0] broadcast = 'h7E;
wire [6:0] my_address = 'h66; //ay kalaaaam

integer count;
reg [19:0] initial_seq;
reg [7:0] deserialized;
reg [7:0] A;
reg [7:0] D1, D2;

reg parity_flag; //to distinguish parity is calculated for cmd or data
reg rnw_flag;
reg first_byte_full;

wire seq_P1, seq_P0;
wire CMD_P1, CMD_P0;
wire D_P1, D_P0;
wire [1:0] Parity;
wire decision_error;

assign seq_P1 = initial_seq[17] ^ initial_seq[15] ^ initial_seq[13] ^ initial_seq[11] ^ initial_seq[9] ^ initial_seq[7] ^ initial_seq[5] ^ initial_seq[3];
assign seq_P0 = initial_seq[16] ^ initial_seq[14] ^ initial_seq[12] ^ initial_seq[10] ^ initial_seq[8] ^ initial_seq[6] ^ initial_seq[4] ^ initial_seq[2] ^ 1;
assign CMD_P1 = rnw_flag ^ A[7] ^ A[5] ^ A[3] ^ A[1] ;
assign CMD_P0 = A[6] ^ A[4] ^ A[2] ^ A[0] ^ 1 ;
assign D_P1 = D1[7] ^ D1[5] ^ D1[3] ^ D1[1] ^ D2[7] ^ D2[5] ^ D2[3] ^ D2[1] ;
assign D_P0 = D1[6] ^ D1[4] ^ D1[2] ^ D1[0] ^ D2[6] ^ D2[4] ^ D2[2] ^ D2[0] ^ 1 ;
assign Parity =  parity_flag? {D_P1,D_P0} : {CMD_P1, CMD_P0};
assign decision_error = (initial_seq[19:18] == special_preamble) & (initial_seq[16:10] == 0) & (initial_seq[2] == (^initial_seq[9:3] ^ initial_seq[17]) & (initial_seq[1] == seq_P1) & (initial_seq[0] == seq_P0));
assign o_ddrccc_rnw = initial_seq[17];

always @ (*)
 begin
   if(!decision_error)
    o_engine_decision = 2'b11;
   else  
     begin
       case (initial_seq[9:3])
        broadcast : o_engine_decision = 2'b10;
        my_address : o_engine_decision = 2'b01;
        default : o_engine_decision = 2'b00; //not me
       endcase
     end
  end


always @ (posedge i_sys_clk or negedge i_sys_rst)
 begin
   if(~i_sys_rst) begin 
             o_regfcrc_rx_data_out <= 0;
             o_ddrccc_rx_mode_done <= 0;
             o_ccc_ccc_value <= 0;
             o_ddrccc_error_flag <= 0;
             count <= 0;
             initial_seq <= 0;
             deserialized <= 0;
             A <= 0;
             D1 <= 0;
             D2 <= 0;
             first_byte_full <= 0;       
      end
  
   else if (i_ddrccc_rx_en)
     
     begin
   
  		  o_ddrccc_rx_mode_done <= 0;
		
		  case (i_ddrccc_rx_mode) 
		    
		    //////////////////////////////////////////////
		    
		    initializing : begin
		      
		      if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd19)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              initial_seq['d19 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd19)                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                             end    
		      
		      end
		    //////////////////////////////////////////////
		    
		    pereamble: begin
		      
          if(!(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge))
                             begin                                                                        
                                o_ddrccc_pre <= i_sdahnd_rx_sda;                                    
                                o_ddrccc_rx_mode_done <= 1'b1;
                                rnw_flag <= i_sdahnd_rx_sda;
                             end 
    
		      end
		    
		    /////////////////////////////////////////////
		    
		    deserializing_ccc_value: begin
                            
                            parity_flag <= 1;
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd7)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              o_ccc_ccc_value['d7 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd7)
                               begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                              			 if (!first_byte_full)
			                              begin
			                               D1 <= {o_ccc_ccc_value[7:1],i_sdahnd_rx_sda};
			                               first_byte_full <= 1;
			                              end
			                            else
			                              begin
			                               D2 <= {o_ccc_ccc_value[7:1],i_sdahnd_rx_sda};
			                               first_byte_full <= 0;
			                              end
                               end
                            end
                          end
                            
        //////////////////////////////////////////////
        
        		    check_Parity: begin
                            
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd1)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              deserialized['d1 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd1)
                                begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  if ({deserialized[1],i_sdahnd_rx_sda} == Parity)
                                    o_ddrccc_error_flag = 0;
                                  else
                                    o_ddrccc_error_flag = 1;
                                end
                             end

                            end
		    
		    //////////////////////////////////////////////

        deserializing_data: begin
                            
                            parity_flag <= 1;
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd7)
                                begin
                                  count <= 'b0;
                                  
                                end
                               end

                            else 
                             begin
                              o_regfcrc_rx_data_out['d7 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd7)
                                begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                              			 if (!first_byte_full)
			                              begin
			                               D1 <= {o_regfcrc_rx_data_out[7:1],i_sdahnd_rx_sda};
			                               first_byte_full <= 1;
			                              end
			                            else
			                              begin
			                               D2 <= {o_regfcrc_rx_data_out[7:1],i_sdahnd_rx_sda};
			                               first_byte_full <= 0;
			                              end
			                          end
                             end

                            end
                            
        /////////////////////////////////////////////////
        
        token_CRC: begin
                            
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd3)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              deserialized['d3 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd3)
                               begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  if ({deserialized[3:1],i_sdahnd_rx_sda} == token)
                                    o_ddrccc_error_flag = 0;
                                  else
                                    o_ddrccc_error_flag = 1;
                               end
                             end

                            end
        
        ////////////////////////////////////////////////
        
                CRC_value: begin
                            
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd4)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              deserialized['d4 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd4)
                               begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  if ({deserialized[4:1],i_sdahnd_rx_sda} == i_crc_value)
                                    o_ddrccc_error_flag = 0;
                                  else
                                    o_ddrccc_error_flag = 1;
                               end
                             end

                            end
        
        ///////////////////////////////////////////////
        
                  deserializing_address: begin
                            
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd7)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              deserialized['d7 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd7)
                               begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  if ((deserialized[7:1] == my_address) & (i_sdahnd_rx_sda == 1))
                                    begin
                                      o_ddrccc_error_flag <= 0;
                                      A <= {deserialized[7:1],i_sdahnd_rx_sda};
                                     end 
                                  else
                                    o_ddrccc_error_flag <= 1;
                               end
                             end

                            end
        
        //////////////////////////////////////////////
        
        deserializing_zeros: begin
                            
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd6)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              if(count == 'd6)                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                             end

                            end
        
        ////////////////////////////////////////////////
        
        special_pereamble: begin
                            
                            parity_flag <= 0;
                            if(i_sclgen_scl_neg_edge || i_sclgen_scl_pos_edge)
                               begin                         
                                count <= count + 1; 
                                if(count == 'd1)
                                begin
                                  count <= 'b0;
                                end
                               end

                            else 
                             begin
                              deserialized['d1 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd1)
                               begin                                                   
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  if ({deserialized[1],i_sdahnd_rx_sda} == special_pereamble)
                                    o_ddrccc_error_flag <= 0;
                                  else
                                    o_ddrccc_error_flag <= 1;     
                               end
                             end

                            end
                            
                        endcase                     
        
        /////////////////////////////////////////////////
          
   end
   
 else
   o_ddrccc_rx_mode_done <= 1'b0;
   
  end                         
endmodule
				          
				          



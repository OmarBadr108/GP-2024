module nt_target (
  input        i_sys_clk,
  input        i_sys_rst,
  input        i_engine_en,
  input        i_tx_mode_done,
  input        i_rx_mode_done,
  input        i_rx_pre,
  input        i_rx_error,
  input        i_rx_ddrccc_rnw,
  input        i_frmcnt_last,

  
  output reg       o_tx_en,
  output reg [2:0] o_tx_mode,
  output reg       o_rx_en,
  output reg [3:0] o_rx_mode,
  output reg       o_engine_done,
  output reg       o_sdahand_pp_od,
  output reg       o_frmcnt_en,
  output wire       o_frmcnt_rnw,
  output reg       o_regf_wr_en,
  output reg       o_regf_rd_en,
  output reg [9:0] o_regf_addr,
  output reg       o_bitcnt_en, 
  output reg       o_bitcnt_reset  
  );
  
  assign o_frmcnt_rnw = i_rx_ddrccc_rnw;

  localparam [3:0]  initializing = 'b0000,    
                    pereamble = 'b0001, 
				            deserializing_data = 'b0010, 
				            deserializing_ccc_value = 'b0011, 
				            check_Parity = 'b0100, 
				            token_CRC = 'b0101, 
				            CRC_value = 'b0110, 
				            deserializing_address = 'b0111, 
				            deserializing_zeros = 'b1000, 
				            special_pereamble = 'b1001; 
 
 
 localparam    [2:0]      PREAMBLE_ZERO           = 3'b000  ,   
                          PREAMBLE_ONE            = 3'b001  ,    
                          SERIALIZING_BYTE        = 3'b011  ,
                          CRC_TOKEN               = 3'b010  ,   
                          PAR_VALUE               = 3'b110  ,
                          CRC_VALUE               = 3'b111  ;
                          
 localparam [3:0]   idle = 0, //done          
					          parity = 1, //done
					          sec_stage_first_data_pre = 2, //done            
					          ack = 3, //done
					          first_data_byte = 4, //done
					          second_data_byte = 5, //done
					          third_stage_first_data_pre = 6, //done           
					          abort_bit = 7, //done                               
					          fourth_stage_crc_first_pre = 8, //done
					          fourth_stage_crc_second_pre = 9, //done 
					          token_crc_bits = 10, //done              
					          crc_value_bits = 11, //done
					          delaying = 12;
					          
parameter Start_From = 'd200;

reg    [3:0]         current_state , 
                     next_state ;
                     
reg [9:0] o_regf_addr_temp;
wire mode_done ;
                     
assign mode_done = i_tx_mode_done || i_rx_mode_done ;
                     
 always @(posedge i_sys_clk or negedge i_sys_rst)
 begin
  if(!i_sys_rst)
    current_state <= idle ;
  else
    current_state <= next_state ;
 end 
 
 always @(*)
  begin
    case (current_state)
      
      idle: begin
        
        if(i_engine_en)
          next_state = sec_stage_first_data_pre;
        else
          next_state = idle;
          
        end
      
      sec_stage_first_data_pre: begin
      
        if(mode_done)
          begin
            if(!i_rx_pre)
              next_state = idle;
            else
              next_state = ack;
          end
        else
          next_state = sec_stage_first_data_pre;
          
        end
        
      ack: begin
        if(mode_done)
         begin
           if(i_rx_ddrccc_rnw)
             next_state = first_data_byte;
           else
             next_state = delaying;
         end
        else
          next_state = ack;
        end
      
      delaying: next_state = first_data_byte;
      
      first_data_byte: begin
        if(mode_done)
          next_state = second_data_byte;
        else
          next_state = first_data_byte;
        end
        
      second_data_byte: begin
        if(mode_done)
          next_state = parity;
        else
          next_state = second_data_byte;
        end
          
      parity: begin
        if(mode_done)
          begin
            if(i_frmcnt_last && i_rx_ddrccc_rnw)
              next_state = fourth_stage_crc_first_pre;
            else
              next_state = third_stage_first_data_pre;
          end
        else
          next_state = parity;
        end
        
      third_stage_first_data_pre: begin
        if(mode_done)
         begin
           if(!i_rx_ddrccc_rnw && !i_rx_pre)
               next_state = fourth_stage_crc_second_pre;
             else
               next_state = abort_bit;
            end
         else
           next_state = third_stage_first_data_pre;
         end
         
      abort_bit: begin
        if(mode_done)
          begin
           if((i_rx_ddrccc_rnw && !i_rx_pre) || (!i_rx_ddrccc_rnw && i_frmcnt_last))
             next_state = idle;
           else
             next_state = first_data_byte;
          end
        else
          next_state = abort_bit;
        end
      
      fourth_stage_crc_first_pre: begin
        if(mode_done)
          next_state = fourth_stage_crc_second_pre;
        else
          next_state = fourth_stage_crc_first_pre;
        end
        
      fourth_stage_crc_second_pre: begin
        if(mode_done)
          next_state = token_crc_bits;
        else
          next_state = fourth_stage_crc_second_pre;
        end 
        
      token_crc_bits: begin
        if(mode_done)
          next_state = crc_value_bits;
        else
          next_state = token_crc_bits;
        end 
        
      crc_value_bits: begin
        if(mode_done)
          next_state = idle;
        else
          next_state = crc_value_bits;
        end
        
      default: next_state = idle;            

    endcase    
  end
  
  always @ (*)
   begin
     
     o_tx_en = 0;
     o_rx_en = 0;
     o_engine_done = 0;
     o_sdahand_pp_od = 1; //pp
     o_regf_wr_en = 0;
     o_regf_rd_en = 0;
     o_bitcnt_reset = 0;

     case (current_state)
       
       idle: begin
        o_bitcnt_en = 'b0;
        o_bitcnt_reset = 1;
        o_frmcnt_en = 0;
        o_regf_addr = Start_From;
        o_rx_mode = pereamble;
        o_tx_mode = PREAMBLE_ZERO; 
        if(i_engine_en)
          o_rx_en = 1;
        else
          o_rx_en = 0;
        end
       
       sec_stage_first_data_pre: begin
         o_bitcnt_reset = 0;
         o_bitcnt_en = 'b1;
         o_frmcnt_en = 'b1 ;
         o_rx_mode = pereamble;
         o_tx_mode = PREAMBLE_ZERO;
         if(mode_done)
          begin
           if(i_rx_pre)  
            begin
             o_engine_done = 0; 
             o_tx_en = 1;
             o_rx_en = 0;
            end
           else
            begin
             o_engine_done = 1; //due to framing error
             o_tx_en = 0;
             o_rx_en = 0;
            end
          end
         else
          begin
           o_engine_done = 0;
           o_rx_en = 1;
           o_tx_en = 0;
          end
         end
       
       ack: begin //transition_state
         o_frmcnt_en = 'b1 ;
         o_bitcnt_en = 'b1;
         o_tx_en = 1;
         o_tx_mode = PREAMBLE_ZERO;
         if(!i_rx_ddrccc_rnw)
         begin
          o_regf_wr_en = 1;
          o_regf_rd_en = 0;
         end
       else
         begin
          o_regf_rd_en = 1;
          o_regf_wr_en = 0;  
         end         
         end
      
      delaying: begin
        o_frmcnt_en = 'b1 ;
        o_bitcnt_en = 'b1;
        o_tx_en = 0;
        o_rx_en = 0;
      end
       
      first_data_byte: begin
       o_frmcnt_en = 'b1 ;
       o_bitcnt_en = 'b1;
       o_regf_addr = o_regf_addr_temp;
       o_tx_mode = SERIALIZING_BYTE;
       o_rx_mode = deserializing_data;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_regf_wr_en = 1;
          o_regf_rd_en = 0;
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_regf_rd_en = 1;
          o_regf_wr_en = 0;  
         end               
       end
         
      second_data_byte: begin
       o_frmcnt_en = 'b1 ;
       o_bitcnt_en = 'b1;
       o_regf_addr = o_regf_addr_temp + 1;
       o_tx_mode = SERIALIZING_BYTE;
       o_rx_mode = deserializing_data;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_regf_wr_en = 1;
          o_regf_rd_en = 0;
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_regf_rd_en = 1;
          o_regf_wr_en = 0;  
         end               
       end    
         
      parity: begin
       o_frmcnt_en = 'b1 ;
       o_bitcnt_en = 'b1;
       o_tx_mode = PAR_VALUE;
       o_rx_mode = check_Parity;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_engine_done = (mode_done && i_rx_error)? 1'b1 : 1'b0;
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_engine_done = 0;
         end
       end 
      
    third_stage_first_data_pre: begin 
     o_rx_mode = pereamble; 
     o_bitcnt_en = 'b1;
     o_frmcnt_en = 'b1 ;
     if (mode_done)
       begin
         o_tx_mode = PREAMBLE_ZERO;
         if (!i_rx_ddrccc_rnw && i_frmcnt_last && i_rx_pre)
           begin
            o_tx_en = 1;
            o_rx_en = 0; 
           end
         else
           begin
            o_tx_en = 0;
            o_rx_en = 0; 
           end
         end          
     else
       begin
       o_tx_mode = PREAMBLE_ONE;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0; 
         end
       end
     end 
       
      
      abort_bit: begin //transition
       o_rx_mode = pereamble;
       o_regf_addr = o_regf_addr_temp;
       o_bitcnt_en = 'b1;
       o_frmcnt_en = 'b1 ;
       if(i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_engine_done = (mode_done && !i_rx_pre)? 1'b1 : 1'b0;
          o_tx_mode = SERIALIZING_BYTE;
          o_regf_rd_en = 1;
          if(mode_done && i_rx_pre)
           begin
             o_tx_en = 1;
             o_rx_en = 0;
           end
          else
            begin
             o_rx_en = 1;
             o_tx_en = 0; 
            end
         end
       else
         begin
          o_regf_wr_en = 1;
          o_tx_en = 1;
          o_rx_en = 0;
          o_tx_mode = i_frmcnt_last? PREAMBLE_ZERO : PREAMBLE_ONE;
          o_engine_done = (mode_done && i_frmcnt_last)? 1'b1 : 1'b0;  
         end
       end 
        
      fourth_stage_crc_first_pre: begin
          o_tx_en = 1;
          o_tx_mode = PREAMBLE_ZERO;
          o_rx_mode = pereamble;
          o_bitcnt_reset = 1;
          o_bitcnt_en = 'b0;
          o_frmcnt_en = 'b0 ;
       end
       
      fourth_stage_crc_second_pre: begin    
       o_rx_mode = pereamble;
       o_tx_mode = PREAMBLE_ONE;
       o_bitcnt_en = 'b0;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_engine_done = (mode_done && !i_rx_pre)? 1'b1 : 1'b0; 
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_engine_done = 0;
         end
       end        
       
      token_crc_bits: begin
       o_bitcnt_en = 'b0;
       o_rx_mode = token_CRC;
       o_tx_mode = CRC_TOKEN;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_engine_done = (mode_done && i_rx_error)? 1'b1 : 1'b0; 
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_engine_done = 0;
         end
       end
      
      crc_value_bits: begin
       o_bitcnt_en = 'b0;
       o_rx_mode = CRC_value;
       o_tx_mode = CRC_VALUE;
       if(!i_rx_ddrccc_rnw)
         begin
          o_rx_en = 1;
          o_tx_en = 0;
          o_engine_done = (mode_done || i_rx_error)? 1'b1 : 1'b0; 
         end
       else
         begin
          o_tx_en = 1;
          o_rx_en = 0;
          o_engine_done = (mode_done)? 1'b1 : 1'b0;
         end
       end        
             
     endcase
   end
           
 always @ (posedge i_sys_clk)
  begin
   if((current_state == second_data_byte) && (mode_done))
      o_regf_addr_temp <= o_regf_addr_temp + 2;
   else if (current_state == idle)
    o_regf_addr_temp <= o_regf_addr; 
  end          
         
          
endmodule
              
                                          



  

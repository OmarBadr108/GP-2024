module rx (

input                     i_sys_clk,
input                     i_sys_rst,
input                     i_sclgen_scl,
input                     i_sclgen_scl_pos_edge,
input                     i_sclgen_scl_neg_edge,
input                     i_ddrccc_rx_en,
input                     i_sdahnd_rx_sda,
//input     [4:0]           i_bitcnt_rx_bit_count,
input        [3:0]        i_ddrccc_rx_mode,
input        [4:0]        i_crc_value,
input                     i_crc_valid,

output  reg  [7:0]        o_regfcrc_rx_data_out,
output  reg               o_ddrccc_rx_mode_done,
output  reg               o_ddrccc_pre,
output  reg               o_ddrccc_error,
output  reg               o_crc_en,                 
output  reg               o_crc_data_valid
//output  reg               o_ddrccc_error_done
);








/////////////////////////////////rx modes/////////////////////////////////
localparam [3:0]     
                     PREAMBLE            = 4'd0  ,            
                     DESERIALIZING_BYTE  = 4'd3  ,                   
                     CHECK_TOKEN         = 4'd4  ,
                     CHECK_PAR_VALUE     = 4'd5  ,
                     CHECK_CRC_VALUE     = 4'd6  ,
                     ERROR               = 4'd7  ;



////////////////////////////////////////////////////////////////////////////


reg [5:0]  count;
wire        count_done;
reg [15:0] data_paritychecker;
reg        byte_num;

reg [7:0] o_regfcrc_rx_data_out_temp;
reg [3:0] token_value_temp;
reg [1:0] parity_value_temp;
reg [4:0] CRC_value_temp;
wire [1:0] parity_value_calc;

wire SCL_edges; 

//////////////////////////////parity calc////////////////////////////////////

 assign parity_value_calc[1] =  data_paritychecker[15]^data_paritychecker[13]^data_paritychecker[11]^data_paritychecker[9]^data_paritychecker[7]^data_paritychecker[5]^data_paritychecker[3]^data_paritychecker[1] ;     
 assign parity_value_calc[0] =  data_paritychecker[14]^data_paritychecker[12]^data_paritychecker[10]^data_paritychecker[8]^data_paritychecker[6]^data_paritychecker[4]^data_paritychecker[2]^data_paritychecker[0]^1'b1 ; 


assign count_done = (count==7)? 1'b1:1'b0 ;

assign SCL_edges = (i_sclgen_scl_pos_edge || i_sclgen_scl_neg_edge);


////////////////////////////// Registering data bytes for parity check ////////////////////////////////////

/*
always @(*)  
begin
   if ((byte_num == 0) && (count_done))
    data_paritychecker[15:8] = o_regfcrc_rx_data_out_temp;
   else if ((byte_num == 1) &&  (count_done))
    data_paritychecker[7 :0]  = o_regfcrc_rx_data_out_temp;
   //else
   //data_paritychecker = 0; ////////////////////////////to be revisit 


end
*/
always @(posedge i_sys_clk or negedge i_sys_rst)  
begin
  if(!i_sys_rst)

  begin
    data_paritychecker <= 'b0;
  end

  else if ((byte_num == 0) && (count_done))
   data_paritychecker[15:8] <= o_regfcrc_rx_data_out_temp;

  else if ((byte_num == 1) &&  (count_done))
   data_paritychecker[7 :0]  <= o_regfcrc_rx_data_out_temp;


end






always @(posedge i_sys_clk or negedge i_sys_rst) 
begin

  if (!i_sys_rst) 
   begin

    o_regfcrc_rx_data_out <= 8'd0;  
    o_ddrccc_rx_mode_done <= 1'b0;
    o_ddrccc_pre          <= 1'bz; //should be editted
    o_ddrccc_error        <= 1'b0;
    o_crc_en              <= 1'b0;   
    count                 <= 'b0;
    byte_num              <= 1'b0;
    o_crc_data_valid      <=  'b0;
 // parity_value_temp     <= 1'b0;
 //   o_ddrccc_error_done   <= 1'b0; 

   end


  else if (i_ddrccc_rx_en) 
   begin
    o_regfcrc_rx_data_out <= 8'd0;  
    o_ddrccc_rx_mode_done <= 1'b0;
    //o_ddrccc_pre          <= 1'bz;   //should be editted
    o_ddrccc_error        <= 1'b0;
    o_crc_en              <= 1'b0; 
    //rx_mode_done_flag     <= 1'b0;
   // parity_value_temp     <= 1'b0;
    o_crc_data_valid      <= 1'b0;
  //  o_ddrccc_error_done   <= 1'b0; 

   case(i_ddrccc_rx_mode) 

    PREAMBLE :          begin
                          count                   <= 'b0;
                         if (SCL_edges)
                          begin
                           //o_ddrccc_pre          <= i_sdahnd_rx_sda;
                           //o_ddrccc_rx_mode_done <= 1'b1;
                           //rx_mode_done_flag     <= 1'b1;
                           byte_num               <= 1'b0;
                           count                  <= 'b0;
                          end
                          else 
                          begin
                            o_ddrccc_rx_mode_done <= 1'b1;
                            o_ddrccc_pre          <= i_sdahnd_rx_sda;
                            end
                        end


      DESERIALIZING_BYTE: begin
                            
                            o_ddrccc_rx_mode_done <= 1'b0;
                            o_ddrccc_pre <= 'bz;
                            o_crc_data_valid <= 'b0;
                            o_crc_en         <=  1'b1;
                            
                            if(SCL_edges)
                               begin
                          
                                count <= count + 1; 
                                if(count == 'd7)
                                begin
                                  count <= 'b0;
                                  o_crc_data_valid <= 1'b1;
                                  o_regfcrc_rx_data_out <= o_regfcrc_rx_data_out_temp;
                                  byte_num <= 'b1;
                                end
                               end

                            else 
                             begin
                              o_ddrccc_rx_mode_done <= 1'b0;
                              o_regfcrc_rx_data_out_temp['d7 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd7)                    
                               begin
                                  
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                end

                            end
                          end



    CHECK_TOKEN :       begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;

                         if(SCL_edges)
                          begin
                            count <= count + 1'b1;
                            
                            if(count == 'd3)
                              begin
                               
                                count <= 'b0; 

                               if(token_value_temp != 4'hC)
                                  o_ddrccc_error<=1'b1;
                                else
                                  o_ddrccc_error<=1'b0;
                                  

                              end 
                          
                          end

                          else 
                          begin
                              token_value_temp['d3 - count] <= i_sdahnd_rx_sda;
                              if(count == 'd3)
                                o_ddrccc_rx_mode_done <= 1'b1;
                            
                          end
                        end 
 
    CHECK_PAR_VALUE :    /*  begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;
                         parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;
                         if(SCL_edges)
                          begin
                           parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;                       
                          end
                         else if(count == 'd1)
                                begin
                                  count<=0;
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  //count <= 'b0; 
                                  if(parity_value_calc != parity_value_temp)
                                    o_ddrccc_error<=1'b1;
                                  else
                                    o_ddrccc_error<=1'b0;
                                end 
                         

                          else 
                            begin
                             count <= count + 1'b1;

                              
                              //o_ddrccc_rx_mode_done <= 1'b0; 
                            end
                        end*/
                        begin
                         //count <= 'b0;
                         o_ddrccc_rx_mode_done <= 1'b0;

                         if(SCL_edges)
                          begin
                           parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;

                             
                          end
                          else  if(count == 'd1)
                                begin
                                  o_ddrccc_rx_mode_done <= 1'b1;
                                  count <= 'b0; 
                                  if(parity_value_calc != parity_value_temp)
                                    o_ddrccc_error<=1'b0;                    //TO BE IDETED// //IMPORTAANNTT//
                                  else
                                    o_ddrccc_error<=1'b0;
                                end 
                          else 
                            begin
                              count <= count + 1'b1;
                               parity_value_temp['d1 - count] <= i_sdahnd_rx_sda;
                              //o_ddrccc_rx_mode_done <= 1'b0; 
                            end
                        end 
 
 
 
    CHECK_CRC_VALUE :   begin

                         //count <= 'b0;
                         o_crc_en<=1'b1;

                         if(SCL_edges)
                           begin
                              count <= count + 1'b1;   
                              
                              if(count == 'd4)
                                begin
                                 count <= 'b0;
                                 if(i_crc_valid)
                                 begin
                                  if(CRC_value_temp != i_crc_value)    
                                     o_ddrccc_error<=1'b0;                  //TO BE IDETED// //IMPORTAANNTT//
                                  else
                                     o_ddrccc_error<=1'b0;
                                 end
                                 end 
                           end
                          
                          else 
                           begin
                           CRC_value_temp['d4 - count] <= i_sdahnd_rx_sda;
                           if(count == 'd4)
                                  o_ddrccc_rx_mode_done <= 1'b1;
                           
                           end
                         
                        end


      ERROR:        begin                              //error state: to be revisit during target design//
                     

                     if (SCL_edges)
                      begin
                          count <= count + 1'b1;
                          /*if(!i_sdahnd_rx_sda)
                           count <=1'b0;*/
                      end
                     else if (!i_sdahnd_rx_sda)
                      begin 
                    
                       o_ddrccc_rx_mode_done <= 1'b0; 
                     //  o_ddrccc_error_done<=1'b0;
                       count <= 'b0;
                      end    
                  


                   
                     else if (count=='d37)
                        begin 
                    
                         o_ddrccc_rx_mode_done <= 1'b1; 
                        // o_ddrccc_error_done<=1'b1;
                         count <= 'b0;
                        end    
                    end
 
 
 
 
    default:     begin
                 o_regfcrc_rx_data_out <= 8'd0;  
                 o_ddrccc_rx_mode_done <= 1'b0;
                 o_ddrccc_pre          <= 1'b0;
                 o_ddrccc_error        <= 1'b0;
                 o_crc_en              <= 1'b0; 
                 o_crc_data_valid      <= 1'b0; 
               //  o_ddrccc_error_done   <= 1'b0;       
                 end

   
  endcase
 end
end
endmodule

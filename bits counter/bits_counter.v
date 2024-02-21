

module bits_counter(
    input  wire       i_sys_clk             ,
    input  wire       i_rst_n               ,
    input  wire       i_bitcnt_en           ,  
    input  wire       i_scl_pos_edge        ,  
    input  wire       i_scl_neg_edge        ,  
    output reg  [4:0] o_cnt_bit_count = 5'd0
    );

// COUNTER CORE

always @(posedge i_sys_clk or negedge i_rst_n) begin 
    if(~i_rst_n) begin
        o_cnt_bit_count <= 0 ;
    end 
    else begin 
        if (i_bitcnt_en) begin 
            if (i_scl_neg_edge || i_scl_pos_edge) begin 
                if (o_cnt_bit_count == 5'd20) begin 
                    o_cnt_bit_count <= 5'd0 ;                     // from 0 to 19 it won't reach 20 
                end
                else begin 
                    o_cnt_bit_count <= o_cnt_bit_count + 1 ; 
                end  
            end 
        end 
        else begin 
            o_cnt_bit_count <= 5'd0 ;
        end 
    end
end
endmodule 
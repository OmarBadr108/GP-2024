module bits_counter(
    input  wire       i_sys_clk              ,
    input  wire       i_rst_n                ,
    input  wire       i_bitcnt_en            ,  
    input  wire       i_scl_pos_edge         ,  
    input  wire       i_scl_neg_edge         , 
    input  wire       i_cccnt_err_rst        , 
    output reg        o_frcnt_toggle         ,
    output reg  [5:0] o_cnt_bit_count = 6'd0
    );

reg [5:0] err_count = 6'd0 ;
////////////////////////////////////// there is 2 versions of the bits counter uncomment only one of them ////////////////////////////////////////


// sequential version the counter is incremented in the middle of the SCL period 

always @(posedge i_sys_clk or negedge i_rst_n) begin 
    if(~i_rst_n) begin
        o_cnt_bit_count <= 0 ;
    end 
    else begin 
        if (i_cccnt_err_rst) begin 
            if (i_scl_neg_edge || i_scl_pos_edge) begin 
                if (err_count == 6'd37) begin 
                    err_count <= 6'd0 ;                     // from 0 to 37 it won't reach 38 
                end
                else begin 
                    err_count <= err_count + 1 ; 
                end  
            end
        o_cnt_bit_count <= err_count ;
        
        end 

        else if (i_bitcnt_en) begin 
            if (i_scl_neg_edge || i_scl_pos_edge) begin 
                if (o_cnt_bit_count == 6'd19) begin 
                    o_cnt_bit_count <= 6'd0 ;                     // from 0 to 19 it won't reach 20 
                end
                else begin 
                    o_cnt_bit_count <= o_cnt_bit_count + 1 ; 
                end  
            end 
        end 
        else begin 
            o_cnt_bit_count <= 6'd0 ;
        end 
    end
end

always @(negedge i_sys_clk) begin 
    if ((o_cnt_bit_count == 'd9 || o_cnt_bit_count == 'd19) && (!i_scl_pos_edge && !i_scl_neg_edge)) begin
        o_frcnt_toggle = 1'b1 ;
    end
    else begin 
        o_frcnt_toggle = 1'b0 ;
    end 
end

endmodule 
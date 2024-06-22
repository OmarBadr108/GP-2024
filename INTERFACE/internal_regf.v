module Internal_Regfile #(parameter WIDTH = 8 , ADDR = 5)
(
    input wire clk,                
    input wire reset,              
    input wire              wr_en,     // Write enable
    input wire              rd_en,     // Read enable
    input wire [WIDTH-1 :0] data_in,   // Data input for writing
    input wire [ADDR-1  :0] addr,      // address
    output reg [WIDTH-1 :0] data_out,   // Data output for reading
    // configuration ports 
    input wire              i_engine_Dummy_conf ,  // if 1 it's a dummy conf
    output reg  [15:0]      o_frmcnt_data_len                 ,
    output reg  [2:0]       o_cccnt_CMD_ATTR                  ,
    output reg  [3:0]       o_engine_TID                          ,       
    output reg  [7:0]       o_ccc_CMD                             ,
    output reg  [4:0]       o_cccnt_DEV_INDEX                 ,
    output reg  [2:0]       o_frmcnt_DTT                  ,
    output reg  [2:0]       o_engine_MODE                     ,
    output reg              o_cccnt_RnW                         ,
    output reg              o_cccnt_WROC                      ,
    output reg              o_cccnt_TOC                         ,
    output reg              o_engine_CP                     ,
    output reg              o_cccnt_DBP                                 ,
    output reg              o_cccnt_SRE                                 
  

);

reg [WIDTH-1:0] conf_regfile [(2**ADDR -1):0];          // 32 registers, each 8 bits wide
integer i;

parameter DUMMY_CONFIGURATION = 5'd9 ; 
reg [31:0] DWORD_0_Vector ;
reg [31:0] DWORD_1_Vector ;

always @(posedge clk or negedge reset) begin
    if (!reset) begin  
        for (i = 14; i < (2**ADDR); i = i + 1) begin
            conf_regfile[i] <= 8'b0;
        end
        /////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
                  // DWORD0 for Dummy configuration .. that's a fixed configurations that doesn't change so it's made on the reset condition
                  // so whenever is needed to excute this dummy configuration the engine just has to give the input "i_engine_configuration" a value equals "DUMMY_CONFIGURATION" value .. say 'd 9
                  conf_regfile[DUMMY_CONFIGURATION]     <= 8'b1000_0001 ;      // 9
                  conf_regfile[DUMMY_CONFIGURATION + 1] <= 8'b1000_1111 ;      // 10
                  conf_regfile[DUMMY_CONFIGURATION + 2] <= 8'b0000_0000 ;      // 11
                  conf_regfile[DUMMY_CONFIGURATION + 3] <= 8'b0001_1000 ;      // 12 
                  
                  //location ZERO  = 8'b0 ;
                  conf_regfile[0] <= 8'b0 ;      
                  // location 17 = 1 (write bit) + 7E           >>>> for SDR 
                  conf_regfile[13] <= 8'hFE ;   // 1111_1110

    end
    else begin
        if (wr_en && !rd_en) begin
            conf_regfile[addr] <= data_in;
        end 
        else if (rd_en && !wr_en) begin 
            data_out <= conf_regfile[addr];
        end


    end     
end

always @(posedge clk) begin
   
        /////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
                o_frmcnt_data_len <= DWORD_1_Vector [31:16] ;

                o_cccnt_CMD_ATTR  <= DWORD_0_Vector [2:0]   ; 
                o_engine_TID      <= DWORD_0_Vector [6:3]   ;
                o_ccc_CMD         <= DWORD_0_Vector [14:7]  ;
                o_engine_CP       <= DWORD_0_Vector [15]    ;
                o_cccnt_DEV_INDEX <= DWORD_0_Vector [20:16] ;
                o_frmcnt_DTT      <= DWORD_0_Vector [25:23] ;
                o_engine_MODE     <= DWORD_0_Vector [28:26] ;
                o_cccnt_RnW       <= DWORD_0_Vector [29]    ;
                o_cccnt_WROC      <= DWORD_0_Vector [30]    ;
                o_cccnt_TOC       <= DWORD_0_Vector [31]    ;

                if (DWORD_0_Vector [0] == 1'b1) begin                     // immediate 
                    o_frmcnt_DTT      <= DWORD_0_Vector [25:23] ;
                    o_cccnt_DBP       <= 1'b0 ;
                    o_cccnt_SRE       <= 1'b0 ;
                end
                else begin                                                                              // regular 
                    o_cccnt_DBP       <= DWORD_0_Vector [25] ;
                    o_cccnt_SRE       <= DWORD_0_Vector [24] ;
                    o_frmcnt_DTT      <= 'd0 ;
                end  

                //reg_array [i_engine_configuration - 1] = 8'b0000_0000 ; //zerozzzz location to ba serialized in ZEROS state 

            //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

end

/////////////////////////////////////////////      HDR     ///////////////////////////////////////////////////////
always @(*) begin 
    if (!i_engine_Dummy_conf) begin              // Normal configuration
        DWORD_0_Vector [7:0]   = conf_regfile [1] ;
        DWORD_0_Vector [15:8]  = conf_regfile [2] ;
        DWORD_0_Vector [23:16] = conf_regfile [3] ;  
        DWORD_0_Vector [31:24] = conf_regfile [4] ;  

        DWORD_1_Vector [7:0]   = conf_regfile [5] ;
        DWORD_1_Vector [15:8]  = conf_regfile [6] ;
        DWORD_1_Vector [23:16] = conf_regfile [7] ;  
        DWORD_1_Vector [31:24] = conf_regfile [8] ; 
    end 
    else begin 
        DWORD_0_Vector [7:0]   = conf_regfile [9] ;
        DWORD_0_Vector [15:8]  = conf_regfile [10] ;
        DWORD_0_Vector [23:16] = conf_regfile [11] ;  
        DWORD_0_Vector [31:24] = conf_regfile [12] ;  

        DWORD_1_Vector [7:0]   = conf_regfile [13] ;
        DWORD_1_Vector [15:8]  = conf_regfile [14] ;
        DWORD_1_Vector [23:16] = conf_regfile [15] ;  
        DWORD_1_Vector [31:24] = conf_regfile [16] ; 
    end 
end 


endmodule
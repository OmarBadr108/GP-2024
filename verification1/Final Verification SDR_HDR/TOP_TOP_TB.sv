module TOP_TOP_TB ();
    logic           i_sdr_clk = 0            ; // system clk
    logic           i_sdr_rst_n              ; // asynch neg edge reset
    logic           i_controller_en          ;// from device configuration of Controller/Target role
    logic           i_i3c_i2c_sel            ; // sdr/i2c blocks selector
    logic           i_ccc_en_dis_hj          ; // (TBD) for enable/disable events to prevent Bus-Initialization or DAA interruptions. 
    logic           i_sclgen_rst_n           ; // new by badr 
    // Configurations signals
    logic   [7:0]   i_regf_config            ;
    logic           i_data_config_mux_sel    ;  //1: to write configurations to the controller ,     0:i3c blocks to access reg file  
    logic   [11:0]  i_regf_wr_address_config ;
    logic           i_regf_wr_en_config      ;
    logic           i_regf_rd_en_config      ; // no need >> to be removed 

    logic           sda                      ; // sda line
    wire            scl                      ; // scl bus

    wire            o_sdr_rx_valid           ; // output to host >> valid data are loaded
    wire            o_ctrl_done              ; // sdr block done signal


// DUT instantiation 
sdr_hdr_transition_top DUT (.*) ; // instatiation by name 

    // system clk = 50 Mhz
    parameter CLK_PERIOD = 20 ;              
    always #(CLK_PERIOD/2) i_sdr_clk = ~i_sdr_clk ;

    parameter configuration   = 1'b1 ;
    parameter Design          = 1'b0 ;
    parameter config_location = 12'd1000 ;
    
    parameter [2:0] RAND_CMD_ATTR  = 'd0   ;
    parameter [3:0] RAND_TID       = 'd3   ;
    parameter [7:0] RAND_CMD       = 8'h00 ;
    parameter       RAND_CP        = 0     ;
    parameter [4:0] RAND_DEV_INDEX = 'd3   ;
    parameter [1:0] RAND_RESERVED  = 'd0   ;
    parameter [2:0] RAND_DTT       = 'd2   ;
    parameter [2:0] RAND_MODE      = 'd6   ;
    parameter       RAND_RnW       = 1'b0  ; // write   
    parameter       RAND_WROC      = 1'd0  ;
    parameter       RAND_TOC       = 1'b1  ;
    parameter [7:0] RAND_DEF_BYTE  = 'd1   ;
    parameter [7:0] RAND_DATA_TWO  = 'd2   ;
    parameter [7:0] RAND_DATA_THREE= 'd3   ;
    parameter [7:0] RAND_DATA_FOUR = 'd4   ;





    integer i ;



    initial begin 
        i_controller_en = 1'b0 ;
        i_i3c_i2c_sel   = 1'b1 ;
        i_sclgen_rst_n  = 1'b0 ;

        #(10*CLK_PERIOD) ;
        i_sclgen_rst_n  = 1'b0 ;

        system_reset();
        #(10*CLK_PERIOD) ;



        // initialization of the object 
        conf_obj = new();

        //#(period that takes all the SDR operation untill entering HDR with proper driving of the sda line (ACK w kda)); // ask laila 
        switch_muxes(configuration);
        input_configuration ();
        switch_muxes (Design);
        i_controller_en = 1'b1 ;

        #(50000000)






    end 

///////////////////////////////////////////////////// TASKS ///////////////////////////////////////
    task system_reset ;
        begin 
            @(negedge i_sdr_clk)
            i_sdr_rst_n = 1'b0 ;
            #(CLK_PERIOD) i_sdr_rst_n = 1'b1 ;
        end 
    endtask

    task switch_muxes(input selector);
        begin 
            i_data_config_mux_sel = selector ; // 1 for configuration and 0 for design 
        end 
    endtask 

    task input_configuration ();
        begin 
            // Randmoized DWORD 0
            @(negedge i_sdr_clk) ;
            i_regf_wr_en_config      = 1'b1 ;
            i_regf_config            = { RAND_CMD[0] , RAND_TID , RAND_CMD_ATTR } ;
            i_regf_wr_address_config = config_location ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config      = 1'b1 ;
            i_regf_config            = { RAND_CP , RAND_CMD[7:1] } ;
            i_regf_wr_address_config = config_location + 1 ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = { RAND_DTT[0] , RAND_RESERVED , RAND_DEV_INDEX } ;
            i_regf_wr_address_config    = config_location + 2 ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = { RAND_TOC , RAND_WROC , RAND_RnW , RAND_MODE , RAND_DTT[2:1]} ;
            i_regf_wr_address_config    = config_location + 3 ;




            // Randmoized DWORD 1
            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = RAND_DEF_BYTE  ;
            i_regf_wr_address_config    = config_location + 4 ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = RAND_DATA_TWO ;
            i_regf_wr_address_config    = config_location + 5 ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = RAND_DATA_THREE ;
            i_regf_wr_address_config    = config_location + 6 ;

            #(CLK_PERIOD) ;
            i_regf_wr_en_config   = 1'b1 ;
            i_regf_config = RAND_DATA_FOUR ;
            i_regf_wr_address_config    = config_location + 7 ;


            #(CLK_PERIOD) ;

        end 
    endtask 

endmodule

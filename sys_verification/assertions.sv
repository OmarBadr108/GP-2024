	

    parameter scl_pos_wrt_sys_clc = 4 ;         // used in sdr transmission trancking changes every pos edge only of sda 
    parameter scl_pos_neg_wrt_sys_clc = 2 ;     // used in hdr transmission trancking changes every pos or neg edge of sda 

    //////////////////////////////////////////////////// ENTHDR assertion /////////////////////////////////////
    sequence start_bit_1 ;
        (sda_tb == 1'b1 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_2 ;
        start_bit_1 ##(1) (sda_tb == 1'b0 && scl_tb == 1'b1 ); 
    endsequence 

    sequence start_bit_3 ;
        start_bit_2 ##(3) (sda_tb == 1'b0 && scl_tb == 1'b0 ); 
    endsequence

    sequence start_bit_4 ;
        start_bit_3 ##(1) (sda_tb == 1'b1 && scl_tb == 1'b0 ); 
    endsequence

    // end of START condition
    ////////////////////////////////////////////////////////////////////////

    sequence ENTHDR_1 ;                        // first bit of seven E is transmitted above and it's duration is here 
        start_bit_4 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_2 ;                       
        ENTHDR_1 ##(5*scl_pos_wrt_sys_clc) sda_tb == 1'b0 ;
    endsequence

    sequence ENTHDR_3 ;
        ENTHDR_2 ##(4*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence ENTHDR_4 ;
        ENTHDR_3 ##(scl_pos_wrt_sys_clc) sda_tb == 1'b0;
    endsequence

    sequence START_ENTHDR_sec;
        ENTHDR_4 ##(6*scl_pos_wrt_sys_clc) sda_tb == 1'b1 ; // this is the first bit in the HDR mode i.e (RnW bit)
    endsequence



    // Property to track SDA line ENTHDR frame >> (8'b11111100 then 9'b001000000) then HDR 
    property START_ENTHDR_sec  ;
        @(posedge i_sdr_clk_tb) $rose(i_controller_en_tb) |-> START_ENTHDR_sec ;
    endproperty


    // Assert the property
    assert property(START_ENTHDR_sec)
                            $display("%t START_ENTHDR_sec PASSED ",$time); else
                            $display("%t START_ENTHDR_sec FAILED ",$time);



///////////////////////////////// HDR ASSERTIONS ////////////////////////////////////

    // CMD word 01_00000000 11111100 11     is shared in all write sequences 

    sequence CMD_WORD_0 ;
        sda_tb == 1'b0 ;
    endsequence

    sequence CMD_WORD_1 ;
        CMD_WORD_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence CMD_WORD_2 ;
        CMD_WORD_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1'b0 ;
    endsequence

    sequence CMD_WORD_3 ; 
        CMD_WORD_2 ##(8*scl_pos_neg_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence CMD_WORD_4 ; 
        CMD_WORD_3 ##(6*scl_pos_neg_wrt_sys_clc) sda_tb == 1'b0 ;
    endsequence
    
    sequence CMD_WORD_5 ; 
        CMD_WORD_4 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1'b1 ;
    endsequence

    sequence CMD_WORD_6 ; 
        CMD_WORD_5 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////

    //////////////////////////////////// BROADCAST //////////////////////////////////////

    // ENEC    Broadcast 10_00000000 00000000 00
    sequence ENEC_B_0 ; 
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence ENEC_B_1 ; // this sequence to be called 
        ENEC_B_0 ##(19*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // first preamble of repeated data word // jump here
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////

    // DISEC   Broadcast 10_00000001 00000000 01
    sequence DISEC_B_0 ;
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence DISEC_B_1 ;
        DISEC_B_0 ##(8*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence DISEC_B_2 ;
        DISEC_B_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence DISEC_B_3 ;
        DISEC_B_2 ##(9*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence DISEC_B_4 ; // this sequence to be called 
        DISEC_B_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // first preamble of repeated data word // jump here
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////
    
    // SETMWL  Broadcast 10_00001001 00000000 11
    sequence SETMWL_B_0 ;
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMWL_B_1 ;
        SETMWL_B_0 ##(5*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMWL_B_2 ;
        SETMWL_B_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMWL_B_3 ;
        SETMWL_B_2 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMWL_B_4 ;
        SETMWL_B_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMWL_B_5 ;
        SETMWL_B_4 ##(8*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMWL_B_6 ;
        SETMWL_B_5 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // first preamble of repeated data word // jump here
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////
    
    // SETMRL  Broadcast 10_00001010 00000000 00
    sequence SETMRL_B_0 ;
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMRL_B_1 ;
        SETMRL_B_0 ##(5*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMRL_B_2 ;
        SETMRL_B_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMRL_B_3 ;
        SETMRL_B_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMRL_B_4 ;
        SETMRL_B_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMRL_B_5 ;
        SETMRL_B_4 ##(11*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // first preamble of repeated data word // jump here
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////

    // Dummy   Broadcast 10_00011111 00000000 01
    sequence Dummy_B_0 ;
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence Dummy_B_1 ;
        Dummy_B_0 ##(4*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence Dummy_B_2 ;
        Dummy_B_1 ##(5*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence Dummy_B_3 ;
        Dummy_B_2 ##(9*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence Dummy_B_4 ;
        Dummy_B_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // first preamble of repeated data word // jump here
    endsequence
    ////////////////////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////// Direct ////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////

    
    // ENEC    Direct 10_10000000 00000000 01               0x80
    sequence ENEC_D_0 ; 
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence ENEC_D_1 ; 
        ENEC_D_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence ENEC_D_2 ; 
        ENEC_D_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence ENEC_D_3 ; 
        ENEC_D_2 ##(16*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence ENEC_D_4 ; 
        ENEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // first preamble of crc word
    endsequence

    // CRC prea + C token + value
    sequence CRC_ENEC_D_0 ; //
        ENEC_D_4 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_1 ; //
        CRC_ENEC_D_0 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_2 ; //
        CRC_ENEC_D_1 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;  // end of C token and start of crc value which is "10101"  = 0x15
    endsequence
    sequence CRC_ENEC_D_3 ; //
        CRC_ENEC_D_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_4 ; //
        CRC_ENEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_5 ; //
        CRC_ENEC_D_4 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence CRC_ENEC_D_6 ; //
        CRC_ENEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence CRC_ENEC_D_6 ; //
        CRC_ENEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // setup bit .. end of crc value and beggining of restart pattern // jump here
    endsequence





    // DISEC    Direct 10_10000001 00000000 10              0x81
    sequence DISEC_D_0 ; 
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence DISEC_D_1 ; 
        DISEC_D_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence DISEC_D_2 ; 
        DISEC_D_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence DISEC_D_3 ; 
        DISEC_D_2 ##(6*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence DISEC_D_4 ; 
        DISEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence DISEC_D_5 ; 
        DISEC_D_4 ##(8*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence DISEC_D_6 ; 
        DISEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // last parity
    endsequence
    sequence DISEC_D_7 ; 
        DISEC_D_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // first preamble of crc word
    endsequence

    // CRC prea + C token + value
    sequence CRC_DISEC_D_0 ; //
        DISEC_D_7 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_DISEC_D_1 ; //
        CRC_DISEC_D_0 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_DISEC_D_2 ; //
        CRC_DISEC_D_1 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;  // end of C token and start of crc value which is "01001" = 0x9
    endsequence
    sequence CRC_DISEC_D_3 ; //
        CRC_DISEC_D_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_DISEC_D_4 ; //
        CRC_DISEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_DISEC_D_5 ; //
        CRC_DISEC_D_4 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence CRC_DISEC_D_6 ; //
        CRC_DISEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // setup bit .. end of crc value and beggining of restart pattern // jump here
    endsequence










    // SETMWL    Direct 10_10001001 00000000 00             0x89
    sequence SETMW_D_0 ; 
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMW_D_1 ; 
        SETMW_D_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence SETMW_D_2 ; 
        SETMW_D_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMW_D_3 ; 
        SETMW_D_2 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMW_D_4 ; 
        SETMW_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMW_D_5 ; 
        SETMW_D_4 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMW_D_6 ; 
        SETMW_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMW_D_7 ; 
        SETMW_D_6 ##(10*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // first preamble of crc word
    endsequence

    // CRC prea + C token + value
    sequence CRC_ENEC_D_0 ; //
        ENEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_1 ; //
        CRC_ENEC_D_0 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_2 ; //
        CRC_ENEC_D_1 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;  // end of C token and start of crc value which is 
    endsequence
    sequence CRC_ENEC_D_3 ; //
        CRC_ENEC_D_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_4 ; //
        CRC_ENEC_D_3 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_5 ; //
        CRC_ENEC_D_4 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence CRC_ENEC_D_6 ; //
        CRC_ENEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // setup bit .. end of crc value and beggining of restart pattern // jump here
    endsequence


    // SETMRL    Direct 10_10001010 00000000 11              0x8A
    sequence SETMRL_D_0 ; 
        CMD_WORD_6 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMRL_D_1 ; 
        SETMRL_D_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence SETMRL_D_2 ; 
        SETMRL_D_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SETMRL_D_3 ; 
        SETMRL_D_2 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMRL_D_4 ; 
        SETMRL_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMRL_D_5 ; 
        SETMRL_D_4 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMRL_D_6 ; 
        SETMRL_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; 
    endsequence
    sequence SETMRL_D_7 ; 
        SETMRL_D_6 ##(9*scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence SETMRL_D_8 ; 
        SETMRL_D_7 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // first preamble of crc word
    endsequence


    // CRC prea + C token + value
    sequence CRC_ENEC_D_0 ; //
        ENEC_D_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_1 ; //
        CRC_ENEC_D_0 ##(3*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_2 ; //
        CRC_ENEC_D_1 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;  // end of C token and start of crc value which is "01101"
    endsequence
    sequence CRC_ENEC_D_3 ; //
        CRC_ENEC_D_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence CRC_ENEC_D_4 ; //
        CRC_ENEC_D_3 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence CRC_ENEC_D_5 ; //
        CRC_ENEC_D_4 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; 
    endsequence
    sequence CRC_ENEC_D_6 ; //
        CRC_ENEC_D_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ; // setup bit .. end of crc value and beggining of restart pattern // jump here
    endsequence



    ///////////////////////////////////////////// Direct GET ////////////////////////////////////////




















    sequence RESTART_PATTERN_0 ; 
        sda_tb == 1 ;
    endsequence
    sequence RESTART_PATTERN_1 ; 
        RESTART_PATTERN_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence RESTART_PATTERN_2 ; 
        RESTART_PATTERN_1 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence RESTART_PATTERN_3 ; 
        RESTART_PATTERN_2 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence RESTART_PATTERN_4 ; 
        RESTART_PATTERN_3 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence RESTART_PATTERN_5 ; 
        RESTART_PATTERN_4 ##(2*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // end of restart pattern and beggining of command word
    endsequence


    ////// second CMD word (only the first half of it)
    sequence SEC_CMD_WORD_0 ; 
        RESTART_PATTERN_5 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 1 ;
    endsequence
    sequence SEC_CMD_WORD_1 ; 
        SEC_CMD_WORD_0 ##(scl_pos_neg_wrt_sys_clc) sda_tb == 0 ;
    endsequence
    sequence SEC_CMD_WORD_2 ; 
        SEC_CMD_WORD_1 ##(7*scl_pos_neg_wrt_sys_clc) sda_tb == 0 ; // then the target address which is randomized .. my job is done here 
    endsequence



















    ////////////////////////////////////////////////// ENDING SEQUENCE ////////////////////////////////////////////////////

        ///////////////////////////////////////////// BROADCAST  //////////////////////////////////////////////////////////
        // for TOC = 0
        sequence restart_pattern_seq ;
            value_CRC_seq ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
        endsequence
        sequence broadcast_sec_TOC_0 ;
            restart_pattern_seq ##(13) o_tx_mode_tb == special_preamble  ;
        endsequence


        // for TOC = 1 
        sequence exit_pattern_seq ;
            value_CRC_seq ##(5*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern ;
        endsequence
        sequence broadcast_sec_TOC_1 ;
            exit_pattern_seq ##(18) o_tx_mode_tb == special_preamble  ;
        endsequence




        //////////////////////////////////////////////////// Dummy assertions /////////////////////////////////////
        // First CMD word
    // Sequence for special preamble
    sequence special_preamble_seq_dummy;
        o_tx_mode_tb == special_preamble;
    endsequence

    sequence zero_after_delay_dummy;
        special_preamble_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == zero;
    endsequence

    sequence seven_zeros_seq_dummy;
        zero_after_delay_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == seven_zeros;
    endsequence

    sequence serializing_byte_port_1_seq_dummy;
        seven_zeros_seq_dummy ##(7*scl_wrt_sys_clk) o_tx_mode_tb == serializing_address;
    endsequence

    sequence parity_calc_seq_dummy;
        serializing_byte_port_1_seq_dummy ##(8 * scl_wrt_sys_clk) o_tx_mode_tb == parity_calc;
    endsequence

    

    // CCC + DEF DATA WORD
    sequence pre_one_sec_dummy ;
        parity_calc_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == one;
    endsequence

    sequence pre_two_1_sec_dummy ;
        pre_one_sec_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == special_preamble ;
    endsequence

    sequence serializing_byte_port_2_seq_dummy ;
        pre_two_1_sec_dummy ##(scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_port ;
    endsequence

    sequence serializing_byte_regf_seq_dummy ;
        serializing_byte_port_2_seq_dummy ##(8*scl_wrt_sys_clk) o_tx_mode_tb == serializing_byte_regf ;
    endsequence

    sequence parity_calc_2_seq_dummy ;
        serializing_byte_regf_seq_dummy ##(8*scl_wrt_sys_clk) o_tx_mode_tb == parity_calc ;
    endsequence



    // crc data word 
    sequence special_preamble_2_sec_dummy ;
        parity_calc_2_seq_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == special_preamble;
    endsequence

    sequence c_token_CRC_seq_dummy ;
        special_preamble_2_sec_dummy ##(2*scl_wrt_sys_clk) o_tx_mode_tb == c_token_CRC ;
    endsequence

    sequence value_CRC_seq_dummy ;
        c_token_CRC_seq_dummy ##(4*scl_wrt_sys_clk) o_tx_mode_tb == value_CRC ;
    endsequence

        
        // for TOC = 0
        sequence restart_pattern_seq_dummy ;
            value_CRC_seq_dummy ##(5*scl_wrt_sys_clk) o_tx_mode_tb == restart_pattern ;
        endsequence
        sequence Dummy_sec_TOC_0 ;
            restart_pattern_seq_dummy ##(13) o_tx_mode_tb == special_preamble  ;
        endsequence


        // for TOC = 1 
        sequence exit_pattern_seq_dummy ;
            value_CRC_seq_dummy ##(5*scl_wrt_sys_clk) o_tx_mode_tb == exit_pattern ;
        endsequence
        sequence Dummy_sec_TOC_1 ;
            exit_pattern_seq_dummy ##(18) o_tx_mode_tb == special_preamble  ;
        endsequence


    // Property to combine all sequences
    // ENEC & DISEC 
    property Broadcast_ENEC_DISEC_TOC_0 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                  (i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 ) && 
                                                    i_regf_DTT_tb == 3'd1             && 
                                                    i_regf_TOC_tb == 0                     ) |-> broadcast_sec_TOC_0 ;
    endproperty


    property Broadcast_ENEC_DISEC_TOC_1 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                  (i_regf_CMD_tb == 8'h00 || i_regf_CMD_tb == 8'h01 ) && 
                                                    i_regf_DTT_tb == 3'd1             && 
                                                    i_regf_TOC_tb == 1                     ) |-> broadcast_sec_TOC_1 ;
    endproperty



    // SETMWL & SETMRL 
    property Broadcast_SETMWL_SETMRL_TOC_0 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                  (i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A ) && 
                                                    i_regf_DTT_tb == 3'd2             && 
                                                    i_regf_TOC_tb == 0                     ) |-> broadcast_sec_TOC_0 ;
    endproperty


    property Broadcast_SETMWL_SETMRL_TOC_1 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                  (i_regf_CMD_tb == 8'h09 || i_regf_CMD_tb == 8'h0A ) && 
                                                    i_regf_DTT_tb == 3'd2             && 
                                                    i_regf_TOC_tb == 1                     ) |-> broadcast_sec_TOC_1 ;
    endproperty



    // Dummy CCC 0x1F 
    property Broadcast_Dummy_TOC_0 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                                    (i_regf_CMD_tb == 8'h1F)          && 
                                                    i_regf_DTT_tb == 3'd0             && 
                                                    i_regf_TOC_tb == 0                     ) |-> Dummy_sec_TOC_0 ;
    endproperty


    property Broadcast_Dummy_TOC_1 ;
        @(negedge i_sys_clk_tb) ($rose(i_engine_en_tb)                                &&
                                                    i_regf_CMD_ATTR_tb  == 3'd1       && 
                                                    (i_regf_CMD_tb == 8'h1F)          && 
                                                    i_regf_DTT_tb == 3'd0             && 
                                                    i_regf_TOC_tb == 1                     ) |-> Dummy_sec_TOC_1 ;
    endproperty




    // Assert the property
    assert property(Broadcast_ENEC_DISEC_TOC_0)
                            $display("%t Broadcast_ENEC_DISEC_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_TOC_0 FAILED ",$time);

    // Assert the property
    assert property(Broadcast_ENEC_DISEC_TOC_1)
                            $display("%t Broadcast_ENEC_DISEC_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_ENEC_DISEC_TOC_1 FAILED ",$time);

    // Assert the property
    assert property(Broadcast_SETMWL_SETMRL_TOC_0)
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_0 FAILED ",$time);

    // Assert the property
    assert property(Broadcast_SETMWL_SETMRL_TOC_1)
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_SETMWL_SETMRL_TOC_1 FAILED ",$time);

    // Assert the property
    assert property(Broadcast_Dummy_TOC_0)
                            $display("%t Broadcast_Dummy_TOC_0 PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_0 FAILED ",$time);

    // Assert the property
    assert property(Broadcast_Dummy_TOC_1)
                            $display("%t Broadcast_Dummy_TOC_1 PASSED ",$time); else
                            $display("%t Broadcast_Dummy_TOC_1 FAILED ",$time);                     


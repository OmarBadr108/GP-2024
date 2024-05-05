library verilog;
use verilog.vl_types.all;
entity Exit_Detector is
    port(
        i_sys_clk       : in     vl_logic;
        i_sys_rst       : in     vl_logic;
        i_cccnt_enable  : in     vl_logic;
        i_scl           : in     vl_logic;
        i_sda           : in     vl_logic;
        o_cccnt_done    : out    vl_logic
    );
end Exit_Detector;

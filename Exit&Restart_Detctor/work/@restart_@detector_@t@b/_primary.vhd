library verilog;
use verilog.vl_types.all;
entity Restart_Detector_TB is
    generic(
        CLK_PERIOD      : integer := 10
    );
    attribute mti_svvh_generic_type : integer;
    attribute mti_svvh_generic_type of CLK_PERIOD : constant is 1;
end Restart_Detector_TB;

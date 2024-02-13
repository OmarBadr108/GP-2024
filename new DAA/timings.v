//////////////////////////////////////////////////////////////////////////////////
//==================================================================================
// MIXEL GP 2023 LIBRARY
// Copyright (c) 2023 Mixel, Inc.  All Rights Reserved.
// CONFIDENTIAL AND PROPRIETARY SOFTWARE/DATA OF MIXEL and ASU 2023 GP, INC.
//
// Authors:  Nour Eldeen Samir  
// Revision: 
//
//----------------------------------------------------------------------------------
// this is not a design file , this file contains local parameters for i3c_timer 
//==================================================================================
//////////////////////////////////////////////////////////////////////////////////


// system clock is 50 MHZ >> period is 20 ns 
// T_ENTAS3 is default when no target supports ENTASx CCC

// -- Start and Stop timings 
localparam T_CAS            = 24'd2       ; // 38.4 ns ~ 40 ns //garanteed
//localparam T_CBP            = 24'd1       ; // 19.2 ns ~ 20 ns //garanteed 

// -- Bus Condition timings
// T_AVAL = T_ENTAS0 = T_NEWCRLOCK_I3C = 1 us
localparam T_BUF_FM         = 24'd25      ; // 0.5 us = 500 ns >> 500/20 = 25 cycles 
localparam T_BUF_FM_P       = 24'd65      ; // 1.3 us = 1300 ns >> 1300/20 = 65 cycles 
localparam T_AVAL           = 24'd50      ; // 1 us = 1000 ns >> 1000/20 = 50 cycles
localparam T_IDLE           = 24'd10000   ; // 200 us = 200000 ns >> 200000/20 = 10000

// -- Activity States timings
localparam T_ENTAS1         = 24'd5000    ; // 100 us = 100000 ns >> 100000/20 = 5000 cycles
localparam T_ENTAS2         = 24'd100000  ; // 2 ms = 2000000 ns >> 2000000/20 = 100000 cycles
localparam T_ENTAS3         = 24'd2500000 ; // 50 ms = 50000000 ns >> 50000000/20 = 2500000 cycles 

// -- Control Role Handoff timings
localparam T_CRHPOverlap    = 24'd11      ; // (200 + 12 = 212 ns ~ 200 + 10 = 210 ns) >> 21/2 cycles 
localparam T_NEWCRLOCK_I2C  = 24'd15      ; // 300 ns >> 300/20 = 15 cycles




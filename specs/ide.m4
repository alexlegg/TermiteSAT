divert(`-1')
define(`forloop', `pushdef(`$1', `$2')_forloop($@)popdef(`$1')')
define(`_forloop',
       `$4`'ifelse($1, `$3', `', `define(`$1', incr($1))$0($@)')')
divert`'dnl

ifdef(`NFRAGS', , `define(`NFRAGS', `5')')dnl
/*
1 = k20
2 = k21
3 = k22 (41s)
4 = k23 (1m3s)
5 = k24 (4m44s)
6 = k25

*/

STATE

stFeatures          : {stFeatNone, stFeatWC, stFeatNWC, stFeatXFR};
regFeature          : {regFeatNone, regFeatWC, regFeatNWC, regFeatXFR};
regXFRMode          : {regXFRModeNone, regXFRModePIO_IORDY, regXFRModePIO, regXFRModePIOFlow, regXFRModeMultiDMA, regXFRModeUltraDMA};
regCommand          : {regCommandNone, regCommandReadPIO, regCommandReadDMA, regCommandWritePIO, regCommandWriteDMA, regCommandSetFeat};
stDMA               : {stDMAIdle, stDMAPRDTWritten, stDMARead, stDMAWrite, stDMAReading, stDMAWriting, 
                            stDMASuccess, stDMAFail, stDMASuccessDone, stDMAFailDone, stDMAError};
bmType              : {bmUnknown, bmRead, bmWrite};
bmCmd               : {bmStop, bmStart};

define(`PRDTdef',`PRDT$1   : {PRDT$1Unset, PRDT$1Set, PRDT$1Last};')dnl
forloop(`i', `0', eval(NFRAGS-1), `PRDTdef(i)
')dnl

osState             : {os_init,
                            os_reset,
                            os_write_cache,
                            os_idle,
                            os_read_dev,
                            os_read_pending,
                            os_write_dev,
                            os_write_pending,
                            os_read_ack_succ,
                            os_read_ack_fail,
                            os_write_ack_succ,
                            os_write_ack_fail,
                            os_complete,
                            os_error};

regLBA0             : {regLBA0NotEqual, regLBA0Equal};
regLBA1             : {regLBA1NotEqual, regLBA1Equal};
regLBA2             : {regLBA2NotEqual, regLBA2Equal};

LABEL

tag                 : {write8, write32, reset, read_complete, write_complete, ack_read_succ, ack_read_fail, ack_write_succ, ack_write_fail};
bank                : {device_reg, pci_reg, system_mem};
addr                : uint<8>;
write8_val          : uint<8>;
write32_val         : {write32NotLast, write32Last}

OUTCOME

osReqType           : {read, write};
transSuccess        : bool;

INIT

define(`PRDTinit',`PRDT$1 == PRDT$1Unset &&')dnl
osState == os_init &&
stFeatures == stFeatNone &&
regFeature == regFeatNone &&
regXFRMode == regXFRModeNone &&
regCommand == regCommandNone &&
regLBA0 == regLBA0NotEqual &&
regLBA1 == regLBA1NotEqual &&
regLBA2 == regLBA2NotEqual &&
stDMA == stDMAIdle &&
forloop(`i', `0', eval(NFRAGS-1), `PRDTinit(i)
')dnl
bmType == bmUnknown &&
bmCmd == bmStop

GOAL
osState == os_complete

FAIR 
osState == os_idle ||
stDMA==stDMAWriting ||
stDMA==stDMAReading

CONT
false

LABELCONSTRAINTS
false

TRANS

regFeature := case {
    tag==write8 && bank==device_reg && addr==0x01 && write8_val== 0x02 : regFeatWC;
    tag==write8 && bank==device_reg && addr==0x01 && write8_val== 0x82 : regFeatNWC;
    tag==write8 && bank==device_reg && addr==0x01 && write8_val== 0x03 : regFeatXFR;
    tag==write8 && bank==device_reg && addr==0x01                      : regFeatNone;
    true                                                         : regFeature;
};

regXFRMode := case {
    tag==write8 && bank==device_reg && addr==0x02 && write8_val==0x00  : regXFRModePIO_IORDY;
    tag==write8 && bank==device_reg && addr==0x02 && write8_val==0x01  : regXFRModePIO;
    tag==write8 && bank==device_reg && addr==0x02 && write8_val==0x08  : regXFRModePIOFlow;
    tag==write8 && bank==device_reg && addr==0x02 && write8_val==0x20  : regXFRModeMultiDMA;
    tag==write8 && bank==device_reg && addr==0x02 && write8_val==0x40  : regXFRModeUltraDMA;
    tag==write8 && bank==device_reg && addr==0x02                      : regXFRModeNone;
    true                                                         : regXFRMode;
};

regLBA0 := case {
    osState==os_write_cache && (stFeatures==stFeatXFR)  : regLBA0NotEqual;
    osState==os_complete                                : regLBA0NotEqual;
    tag==write8 && bank==device_reg && addr==0x03             : regLBA0Equal;
    true                                                : regLBA0;
};

regLBA1 := case {
    osState==os_write_cache && (stFeatures==stFeatXFR)  : regLBA1NotEqual;
    osState==os_complete                    : regLBA1NotEqual;
    tag==write8 && bank==device_reg && addr==0x04 : regLBA1Equal;
    true                                    : regLBA1;
};

regLBA2 := case {
    osState==os_write_cache && (stFeatures==stFeatXFR)  : regLBA2NotEqual;
    osState==os_complete                    : regLBA2NotEqual;
    tag==write8 && bank==device_reg && addr==0x05 : regLBA2Equal;
    true                                    : regLBA2;
};

regCommand := case {
    tag==write8 && bank==device_reg && addr==0x07 && write8_val==0x20     : regCommandReadPIO;
    tag==write8 && bank==device_reg && addr==0x07 && write8_val==0xC8     : regCommandReadDMA;
    tag==write8 && bank==device_reg && addr==0x07 && write8_val==0x30     : regCommandWritePIO;
    tag==write8 && bank==device_reg && addr==0x07 && write8_val==0xCA     : regCommandWriteDMA;
    tag==write8 && bank==device_reg && addr==0x07 && write8_val==0xEF     : regCommandSetFeat;
    true                                                                  : regCommandNone;
};

stFeatures := case {
    regCommand == regCommandSetFeat                                 : regFeature;
    true                                                            : stFeatures;
};

/* Bit slices apparently don't work so this looks weird */
bmType := case {
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x00  : bmRead;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x01  : bmRead;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x08  : bmWrite;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x09  : bmWrite;
    true                                                            : bmType;
};

bmCmd := case {
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x00  : bmStop;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x01  : bmStart;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x08  : bmStop;
    tag==write8 && bank==pci_reg && addr==0x00 && write8_val==0x09  : bmStart;
    true                                                            : bmCmd;
};

define(`PRDTset', `PRDT$1 == ifelse($1,eval(NFRAGS-1),PRDT$1Last,PRDT$1Set) &&')dnl
stDMA := case {
    stDMA!=stDMAIdle && tag==write32 && bank==system_mem                : stDMAError;
    !(stDMA == stDMARead ||
      stDMA == stDMAWrite ||
      stDMA == stDMAReading ||
      stDMA == stDMAWriting
    ) && bmCmd == bmStart                                              : stDMAError;
    stDMA==stDMAIdle &&
        forloop(`i', `0', eval(NFRAGS-1), `PRDTset(i)
        ')
        tag==write32 && bank==pci_reg && addr==0x04                     : stDMAPRDTWritten; /* TODO: set last table entry */
    stDMA==stDMAIdle && tag==write32 && bank==pci_reg && addr==0x04     : stDMAError;

    stDMA==stDMAPRDTWritten && regCommand==regCommandReadDMA &&
        (bmType!=bmRead ||
        !(regXFRMode==regXFRModeMultiDMA || regXFRMode==regXFRModeUltraDMA) ||
        regLBA0!=regLBA0Equal ||
        regLBA1!=regLBA1Equal ||
        regLBA2!=regLBA2Equal)                                          : stDMAError;

    stDMA==stDMAPRDTWritten && regCommand==regCommandWriteDMA &&
        (bmType!=bmWrite ||
        !(regXFRMode==regXFRModeMultiDMA || regXFRMode==regXFRModeUltraDMA) ||
        regLBA0!=regLBA0Equal ||
        regLBA1!=regLBA1Equal ||
        regLBA2!=regLBA2Equal)                                          : stDMAError;

    stDMA==stDMAPRDTWritten && regCommand==regCommandReadDMA            : stDMARead;
    stDMA==stDMAPRDTWritten && regCommand==regCommandWriteDMA           : stDMAWrite;
    stDMA==stDMARead && bmType!=bmRead                                  : stDMAError;
    stDMA==stDMAWrite && bmType!=bmWrite                                : stDMAError;
    stDMA==stDMAReading && bmType!=bmRead                               : stDMAError;
    stDMA==stDMAWriting && bmType!=bmWrite                              : stDMAError;
    stDMA==stDMARead && bmCmd==bmStart                                  : stDMAReading;
    stDMA==stDMAWrite && bmCmd==bmStart                                 : stDMAWriting;
    (stDMA==stDMAWriting || stDMA==stDMAReading) && transSuccess==1     : stDMASuccess;
    (stDMA==stDMAWriting || stDMA==stDMAReading) && transSuccess==0     : stDMAFail;
    stDMA==stDMASuccess && bmCmd==bmStop                                : stDMASuccessDone;
    stDMA==stDMAFail && bmCmd==bmStop                                   : stDMAFailDone;
    (stDMA==stDMASuccessDone || stDMA==stDMAFailDone)                   : stDMAIdle;
    true                                                                : stDMA;
};

define(`PRDTtrans',`PRDT$1 := case {
    osState==os_idle && osReqType==read                                         : PRDT$1Unset;
    osState==os_idle && osReqType==write                                        : PRDT$1Unset;
    tag==write32 && bank==system_mem && addr==$1 && write32_val==write32NotLast : PRDT$1Set;
    tag==write32 && bank==system_mem && addr==$1 && write32_val==write32Last    : PRDT$1Last;
    true                                                                        : PRDT$1;
};')dnl
forloop(`i', `0', eval(NFRAGS-1), `PRDTtrans(i)
')dnl

osState := case {
    stDMA==stDMAError : os_error;

    osState==os_init && tag==reset : os_reset;

    osState==os_reset && (stFeatures==stFeatNWC)
            : os_write_cache;

    osState==os_write_cache && (stFeatures==stFeatXFR)
            : os_idle;

    osState==os_idle && osReqType==read : os_read_dev;

    osState==os_idle && osReqType==write : os_write_dev;

    osState==os_read_dev && stDMA==stDMAReading
            : os_read_pending;

    osState==os_read_pending && stDMA==stDMASuccessDone
            : os_read_ack_succ;

    osState==os_read_pending && stDMA==stDMAFailDone
            : os_read_ack_fail;

    osState==os_write_dev && stDMA==stDMAWriting
            : os_write_pending;

    osState==os_write_pending && stDMA==stDMASuccessDone
            : os_write_ack_succ;

    osState==os_write_pending && stDMA==stDMAFailDone
            : os_write_ack_fail;

    osState==os_read_ack_succ && tag==ack_read_succ : os_complete;

    osState==os_read_ack_fail && tag==ack_read_fail : os_complete;

    osState==os_write_ack_succ && tag==ack_write_succ : os_complete;

    osState==os_write_ack_fail && tag==ack_write_fail : os_complete;

    true    : osState;
};

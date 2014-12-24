divert(`-1')
define(`forloop', `pushdef(`$1', `$2')_forloop($@)popdef(`$1')')
define(`_forloop',
       `$4`'ifelse($1, `$3', `', `define(`$1', incr($1))$0($@)')')

define(`size', `ifelse(eval(incr($1) > (2 ** $2)), `1', `size($1, incr($2))', `$2')')
divert`'dnl

ifdef(`FIFOLEN', , `define(`FIFOLEN', `6')')dnl
define(`FIFOSZ', `size(FIFOLEN, 1)')dnl
define(`FIFOMAX', `eval((2 ** FIFOSZ) - 1)')dnl

/*
k = 4 + (4 * LEN)

Example:
E write config reg (dlab to 1)
A uidle
E write config reg (regDLL)
A uidle
E write config reg (regDLM)
A uidle
E write config reg (dlab to 0)
A uidle
E config_complete
A uidle
E idle
A write_nopass
E idle
A write_nopass
E idle
A write_pass
E write THR
A uidle
E send
A uidle
E idle
A write_pass
E write THR
A uidle
E send
A uidle
A write_pass
E write THR
A uidle
E send
*/

STATE

define(`datadef',`data$1 : uint<1>;')dnl
forloop(`i', `0', eval(FIFOLEN-1), `datadef(i)
')dnl

tail            : uint<FIFOSZ>;
remaining_bytes : uint<FIFOSZ>;
ready_bytes     : uint<FIFOSZ>;
pending_bytes   : uint<FIFOSZ>;

err     : bool;
os_err  : bool;
osState : {osInit, osConfig, osIdle};
turn    : {turnOS, turnDRV};

/* Device state */
regTHR  : {regTHRUnset, regTHRSet, regTHRError};
regDLL  : {regDLLUnset, regDLLSet};
regDLM  : {regDLMUnset, regDLMSet};
/* regFCR  : {regFCRDisabled, regFCREnabled};
regLCR  : {regLCRUnset, regLCRSet}; */
dlab    : bool;

LABEL

tag : {idle, send, config_complete, write};
idx : uint<FIFOSZ>;
addr : uint<8>;
val : uint<8>;

OUTCOME

utag        : {uidle, write_pass, write_nopass};

define(`datainit', `data$1 == 0 &&')dnl

INIT
forloop(`i', `0', eval(FIFOLEN-1), `datainit(i)
')dnl
tail == 0 &&
remaining_bytes == FIFOLEN &&
pending_bytes == FIFOLEN &&
ready_bytes == 0 &&
osState == osInit &&
err == 0 &&
os_err == 0 &&
turn == turnDRV &&
regDLL == regDLLUnset &&
regDLM == regDLMUnset &&
regTHR == regTHRUnset &&
/* regFCR == regFCRDisabled &&
regLCR == regLCRUnset && */
dlab == 0

GOAL
os_err == 1 || (regTHR != regTHRError && err == 0 && remaining_bytes == 0)

FAIR
osState == osIdle && turn == turnOS

CONT
false

LABELCONSTRAINTS
false

TRANS

osState := case {
    osState == osInit                               : osConfig;
    osState == osConfig 
        && regDLL == regDLLSet
        && regDLM == regDLMSet
        /* && regFCR == regFCREnabled
        && regLCR == regLCRSet */
        && tag == config_complete                   : osIdle;
    true                                            : osState;
};

define(`datatrans',`data$1 := case {
    osState != osIdle                   : data$1;
    turn == turnOS && (utag == write_nopass || utag == write_pass) && tail == $1    : 1;
    tag == send && idx == $1            : 0;
    true                                : data$1;
};
')dnl
forloop(`i', `0', eval(FIFOLEN-1), `datatrans(i)
')dnl

define(`tailtrans',`turn == turnOS && (utag == write_nopass || utag == write_pass) && tail == $1 : eval($1+1);')dnl
tail := case {
    osState != osIdle : tail;
forloop(`i', `0', eval(FIFOLEN-1), `
    tailtrans(i)')dnl

    true : tail;
};

define(`rbtrans',`remaining_bytes == eval($1+1) && tag == send : $1;')dnl
remaining_bytes := case {
    osState != osIdle                   : remaining_bytes;
forloop(`i', `0', eval(FIFOLEN-1), `
    rbtrans(i)')dnl

    true                                : remaining_bytes;
};

define(`pendingtrans',`turn == turnOS && (utag == write_nopass || utag == write_pass) && pending_bytes == $1 : decr($1);')dnl

pending_bytes := case {
    osState != osIdle                   : pending_bytes;
forloop(`i', `1', FIFOLEN, `
    pendingtrans(i)')dnl

    true                                : pending_bytes;
};

define(`rdytrans',`turn == turnOS && (utag == write_pass || utag == write_nopass) && ready_bytes == $1  : eval($1+1);
    tag == send && ready_bytes == eval($1+1)         : $1;')dnl

ready_bytes := case {
    osState != osIdle                   : ready_bytes;
forloop(`i', `0', eval(FIFOLEN-1), `
    rdytrans(i)')dnl

    true                                    : ready_bytes;
};

turn := case {
    osState != osIdle                       : turnOS; /* Make sure OS starts with control */
    tag == send && pending_bytes != 0       : turnOS; /* Give control back after a send */
    utag == write_pass                      : turnDRV; /* OS can pass control */
    true                                    : turn;
};


define(`errtrans2',`tag == send && idx == $1 && data$2 == ifelse(`$1', `$2', `0', `1')   : 1;')dnl
define(`errtrans',`forloop(`j', `0', `$1', `
    errtrans2($1, j)')')dnl
define(`errtrans3', `tag == send && idx == $1                 : 1;')dnl

err := case {
forloop(`i', `0', eval(FIFOLEN-1), `
    errtrans(i)')dnl

forloop(`i', FIFOLEN, FIFOMAX, `
    errtrans3(i)')dnl

    true                                    : err;
};

os_err := case {
    utag == write_nopass && (pending_bytes == 1 || pending_bytes == 0)  : 1; /* Must pass if we've written everything already */
    true                                                                : os_err;
};

regTHR := case {
    regTHR == regTHRUnset && tag == write && addr == 0x00 && dlab == 0  : regTHRSet;
    regTHR == regTHRSet && tag == write && addr == 0x00 && dlab == 0    : regTHRError;
    regTHR == regTHRUnset && tag == send                                : regTHRError;
    regTHR == regTHRSet && tag == send                                  : regTHRUnset;
    regTHR == regTHRSet && turn == turnOS && 
        (utag == write_pass || utag == write_nopass)                    : regTHRUnset;
    true                                        : regTHR;
};

regDLL := case {
    regDLL == regDLLUnset && tag == write && dlab == 1 && addr == 0x00      : regDLLSet;
    true                                                                    : regDLL;
};

regDLM := case {
    regDLM == regDLMUnset && tag == write && dlab == 1 && addr == 0x01      : regDLMSet;
    true                                                                    : regDLM;
};

/*
regFCR := case {
    tag == write && addr == 0x02 && val == 0x01                             : regFCREnabled;
    tag == write && addr == 0x02 && val == 0x00                             : regFCRDisabled;
    true                                                                    : regFCR;
};

regLCR := case {
    regLCR == regLCRUnset && tag == write && addr == 0x03                   : regLCRSet;
    true                                                                    : regLCR;
}; */

dlab := case {
    tag == write && addr == 0x03 && val == 0x80                             : 1;
    tag == write && addr == 0x03 && val == 0x00                             : 0;
    true                                                                    : dlab;
};
    

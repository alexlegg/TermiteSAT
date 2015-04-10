divert(`-1')
define(`forloop', `pushdef(`$1', `$2')_forloop($@)popdef(`$1')')
define(`_forloop',
       `$4`'ifelse($1, `$3', `', `define(`$1', incr($1))$0($@)')')
divert`'dnl

ifdef(`qlenf', , `define(`qlen', `20')')dnl
define(`qlen', eval(qlenf+1))dnl
STATE

define(`decl_cell',`
dat$1 : bool;
rdy$1 : bool;
fin$1 : bool;')dnl

forloop(`i', `0', eval(qlen-1), `decl_cell(i)')

tail   : uint<8>;
err    : bool;
hw_err : bool;
turn   : bool;

LABEL

// controllable label
ctag : {cidle, write_dat, write_rdy};
idx  : uint<8>;

OUTCOME

// uncontrollable label
utag : {uidle, send_ok_pass, send_ok_nopass, send_fail};

INIT

define(`init_cell',`
(rdy$1 == 0) &&
(fin$1 == 0)')dnl

forloop(`i', `0', eval(qlen-1), `init_cell(i) &&')
(tail   == 0) &&
(err    == 0) &&
(hw_err == 0) &&
(rdy0   == 0) &&
(turn   == 0)

GOAL

define(`goal_cell',`fin$1 == 1')dnl

(err == 0) &&
(hw_err == 1 || 
(forloop(`i', `0', eval(qlen-1), `
    goal_cell(i) ifelse(i, eval(qlen-1),`',`&&')')
))

FAIR 

define(`fair_cell',`(tail == $1) && (rdy$1 == 1) && (hw_err == 0)')dnl

(
forloop(`i', `0', eval(qlen-1), `
    fair_cell(i) ifelse(i, eval(qlen-1), `', `||')')
)
&& (turn == 1)

CONT

false 

LABELCONSTRAINTS

true


TRANS

define(`upd_dat',`dat$1 := case {
    ctag == write_dat && idx == $1: 1;
    true : dat$1;
};')dnl

forloop(`i', `0', eval(qlen-1), `
upd_dat(i)')

define(`upd_rdy',`rdy$1 := case {
    ctag == write_rdy && idx == $1: 1;
    rdy$1 == 1 && tail == $1 && (utag == send_ok_pass || utag == send_ok_nopass || utag == send_fail): 0;
    true : rdy$1;
};')dnl

forloop(`i', `0', eval(qlen-1), `
upd_rdy(i)')

define(`upd_fin',`fin$1 := case {
    rdy$1 == 1 && tail == $1 && (utag == send_ok_pass || utag == send_ok_nopass): 1;
    true : fin$1;
};')dnl

forloop(`i', `0', eval(qlen-2), `
upd_fin(i)')

define(`last_fin', `fin$1 := 0;')dnl

last_fin(eval(qlen-1))

define(`upd_tail',`rdy$1 == 1 && tail == $1 && (utag == send_ok_pass || utag == send_ok_nopass) : eval(($1+1) % qlen);')dnl


tail  := case {
forloop(`i', `0', eval(qlen-1), `    upd_tail(i)
')dnl
    true:  tail;
};


define(`upd_err',`rdy$1 == 1 && tail == $1 && (utag == send_ok_pass || utag == send_ok_nopass) && dat$1 == 0: 1;')dnl

err := case {
forloop(`i', `0', eval(qlen-1), `    upd_err(i)
')dnl
    true:  err;
};


define(`upd_hw_err',`rdy$1 == 1 && tail == $1 && utag == send_fail: 1;')dnl

hw_err := case {
forloop(`i', `0', eval(qlen-1), `    upd_hw_err(i)
')dnl
    true: hw_err;
};

turn := case {
    (ctag != cidle)           : 1;
    (utag == send_ok_pass)    : 0;
    true                      : 1;
};

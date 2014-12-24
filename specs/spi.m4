divert(`-1')
define(`forloop', `pushdef(`$1', `$2')_forloop($@)popdef(`$1')')
define(`_forloop',
       `$4`'ifelse($1, `$3', `', `define(`$1', incr($1))$0($@)')')
divert`'dnl

ifdef(`QSIZE', , `define(`QSIZE', `5')')dnl

define(`state_var', `$1 hide(`: $2;')')dnl
dnl
define(`reqdef',`state_var(req$1, `uint<6>')')dnl
dnl
define(`donedef',`state_var(done$1, `uint<1>')')dnl
dnl
define(`decl_state',`
forloop(`i', `0', eval(QSIZE-1), `reqdef(i)
')dnl
forloop(`i', `0', eval(QSIZE-1), `donedef(i)
')dnl
state_var(cur, uint<6>)
state_var(turn, bool)
state_var(hw_err, bool)')

ifelse(MODE, `VARS', `define(`hide', `')decl_state', `define(`hide', `$1')

STATE

decl_state

LABEL

tag                : {cidle, write, start};
addr               : uint<6>;
val                : uint<6>;

OUTCOME

utag : {uidle, xfer_ok, xfer_err};

INIT

/*
define(`reqinit',`req$1 == 0 &&')dnl
forloop(`i', `0', eval(QSIZE-1), `reqinit(i)
')dnl

define(`doneinit',`done$1 == 0 &&')dnl
forloop(`i', `0', eval(QSIZE-1), `doneinit(i)
')dnl
*/
hw_err == 0 &&
cur == 0 &&
turn == 0

GOAL

define(`donegoal',`done$1 == 1 &&')dnl
(forloop(`i', `0', eval(QSIZE-1), `donegoal(i)
')dnl
true) || hw_err == 1


FAIR 

turn == 1 && cur != QSIZE

CONT

false

LABELCONSTRAINTS
false

TRANS

define(`requpd', `req$1 := case {
    tag == write && addr == $1 : val;
    true : req$1;
};')
forloop(`i', `0', eval(QSIZE-1), `requpd(i)
')dnl

define(`doneupd', `done$1 := case {
forloop(`i', `0', eval(QSIZE-1), `
    turn == 1 && utag == xfer_ok && cur == i && req`'i == eval($1+1) : 1;')
    true : done$1;
};')
forloop(`i', `0', eval(QSIZE-1), `doneupd(i)
')dnl

cur := case {
forloop(`i', `0', eval(QSIZE-1), `
    turn == 1 && cur == i : eval(i+1);')
    true : cur;
};

turn := case {
    tag == start : 1;
    true : turn;
}; 

hw_err := case {
    turn == 1 && utag == xfer_err : 1;
    true : hw_err;
};

')

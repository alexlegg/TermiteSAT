<% qlen = int(param) + 1 %>

STATE

% for i in range(0, qlen):
dat${i} : bool;
rdy${i} : bool;
fin${i} : bool;
% endfor

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

% for i in range(0, qlen):
(rdy${i} == 0) &&
(fin${i} == 0) &&
% endfor

(tail   == 0) &&
(err    == 0) &&
(hw_err == 0) &&
(rdy0   == 0) &&
(turn   == 0)

GOAL

(err == 0) &&
(hw_err == 1 || 
    (
% for i in range(0, qlen):
    fin${i} == 1 \
% if not(loop.last):
&&
% endif
% endfor

    )
)

FAIR 


(
% for i in range(0, qlen):
    (tail == ${i}) && (rdy${i} == 1) && (hw_err == 0) \
% if not(loop.last):
||
% endif
% endfor

)
&& (turn == 1)

CONT

false 

LABELCONSTRAINTS

true


TRANS

% for i in range(0, qlen):
dat${i} := case {
    ctag == write_dat && idx == ${i}: 1;
    true : dat${i};
};
% endfor

% for i in range(0, qlen):
rdy${i} := case {
    ctag == write_rdy && idx == ${i}: 1;
    rdy${i} == 1 && tail == ${i} && (utag == send_ok_pass || utag == send_ok_nopass || utag == send_fail): 0;
    true : rdy${i};
};
% endfor


% for i in range(0, qlen):
fin${i} := case {
    \
% for j in range(0, qlen):
% if not (i == j):
fin${j} == 1 && \
% endif
% endfor
true : fin${i};
    rdy${i} == 1 && tail == ${i} && (utag == send_ok_pass || utag == send_ok_nopass): 1;
    true : fin${i};
};
% endfor

tail  := case {
    % for i in range(0, qlen):
    rdy${i} == 1 && tail == ${i} && (utag == send_ok_pass || utag == send_ok_nopass) : ${(i+1) % qlen};
    % endfor
    true:  tail;
};

err := case {
    % for i in range(0, qlen):
    rdy${i} == 1 && tail == ${i} && (utag == send_ok_pass || utag == send_ok_nopass) && dat${i} == 0: 1;
    % endfor
    true:  err;
};

hw_err := case {
    % for i in range(0, qlen):
    rdy${i} == 1 && tail == ${i} && utag == send_fail: 1;
    % endfor
    true: hw_err;
};

turn := case {
    (ctag != cidle)           : 1;
    (utag == send_ok_pass)    : 0;
    true                      : 1;
};

<%
size        = int(param)
master_bits = (size - 1).bit_length()
%>

STATE
reg_ready           : bool;
fair_cnt            : uint<4>;
o_err               : bool;

% for i in range(0, size):
reg_grant${i}       : bool;
sys_fair${i}_done   : bool;
%endfor

LABEL
ready               : bool;
% for i in range(0, size):
i_req${i}           : bool;
%endfor

OUTCOME
% for i in range(0, size):
grant${i}           : bool;
%endfor
master              : uint<${master_bits}>;

INIT
reg_ready           := 0;
fair_cnt            := 0;
o_err               := 0;

% for i in range(0, size):
reg_grant${i}       := 0;
sys_fair${i}_done   := 0;
%endfor

GOAL
o_err == 1

TRANS
{

reg_ready := ready;

fair_cnt := case {
% for i in range(0, size):
    sys_fair${i}_done == 1 &&
%endfor
        true : 0;
    ready == 1 && fair_cnt == 0                     : 1;
    ready == 1 && fair_cnt == 1                     : 2;
    ready == 1 && fair_cnt == 2                     : 3;
    ready == 1 && fair_cnt == 3                     : 4;
    ready == 1 && fair_cnt == 4                     : 5;
    ready == 1 && fair_cnt == 5                     : 6;
    ready == 1 && fair_cnt == 6                     : 7;
    ready == 1 && fair_cnt == 7                     : 8;
    ready == 1 && fair_cnt == 8                     : 9;
    ready == 1 && fair_cnt == 9                     : 10;
    ready == 1 && fair_cnt == 10                    : 11;
    ready == 1 && fair_cnt == 11                    : 12;
    ready == 1 && fair_cnt == 12                    : 13;
    ready == 1 && fair_cnt == 13                    : 14;
    ready == 1 && fair_cnt == 14                    : 15;
    ready == 1 && fair_cnt == 15                    : 15;
    true                                            : fair_cnt;
};

% for i in range(0, size):
reg_grant${i} := grant${i};
% endfor

% for i in range(0, size):
sys_fair${i}_done := case {
    % for j in range(0, size):
    sys_fair${j}_done == 1 &&
    %endfor
        true                                                        : 0;
    (sys_fair${i}_done == 1) || (master == ${i}) || (i_req${i} == 0)   : 1;
    true                                                            : 0;
};
% endfor

o_err := case {
    % for i in range(0, size):
    !( (reg_ready == 0) || ((reg_grant${i} == 1) <-> (master == ${i}))) : 1;
    %endfor
    fair_cnt == 8 || fair_cnt == 9 || fair_cnt == 10 
        || fair_cnt == 11 || fair_cnt == 12 || fair_cnt == 13
        || fair_cnt == 14 || fair_cnt == 15                             : 1;
    true                                                                : o_err;
};

}

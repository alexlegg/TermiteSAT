<% size = int(param) %>

STATE 
s : uint<${size}>;
turn : uint<1>;

LABEL
c : {c_idle, c_next};

OUTCOME
u : {u_idle, u_win, u_lose};

INIT
s == 0 && turn == 0

GOAL
s == ${(2**size) - 1}

FAIR
turn == 1

CONT
false

LABELCONSTRAINTS
false

TRANS

turn := case {
    turn == 0 : 1;
    turn == 1 : 0;
};

s := case {
    % for i in range(0, (2**size) - 1):
    s == ${i} && c == c_next : ${i+1};
    % endfor

    u == u_win  : ${(2**size) - 1};
    u == u_lose : s;

    true : s;
}

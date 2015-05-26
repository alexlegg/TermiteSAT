module test(
    o_err,
    i_clk,
    i_req0,
    i_req1,
    i_ready,
    controllable_grant0,
    controllable_grant1,
    controllable_master);

input i_clk;
input i_ready;
input i_req0;
input i_req1;
input i_req2;
input controllable_grant0;
input controllable_grant1;
input controllable_grant2;
input [1:0] controllable_master;
output o_err;

reg reg_ready;
reg reg_grant0;
reg reg_grant1;
reg reg_grant2;
reg [3:0] fair_cnt;
reg sys_fair1_done;
reg sys_fair2_done;
reg sys_fair3_done;
reg env_fair1_done;

wire sys_safety1;
wire sys_safety2;
wire sys_safety3;
wire sys_fair1;
wire sys_fair2;
wire sys_fair3;
wire env_fair1;
wire fair_err;
wire o_err;

// G . ready -> (grant[i] <-> X(master = i))
assign sys_safety1 = ~( ~(reg_ready) | (reg_grant0 ^~ (controllable_master == 2'b00)));
assign sys_safety2 = ~( ~(reg_ready) | (reg_grant1 ^~ (controllable_master == 2'b01)));
assign sys_safety3 = ~( ~(reg_ready) | (reg_grant2 ^~ (controllable_master == 2'b10)));

assign sys_fair1 = ( (controllable_master == 2'b00) | (~i_req0) );
assign sys_fair2 = ( (controllable_master == 2'b01) | (~i_req1) );
assign sys_fair3 = ( (controllable_master == 2'b10) | (~i_req2) );

assign env_fair1 = i_ready;

assign fair_err = fair_cnt >= 4'b0100;

assign o_err = sys_safety1 | sys_safety2 | sys_safety3 | fair_err;

initial
begin
    reg_ready = 0;
    reg_grant0 = 0;
    reg_grant1 = 0;
    reg_grant2 = 0;
    fair_cnt = 0;
    sys_fair1_done = 0;
    sys_fair2_done = 0;
    sys_fair3_done = 0;
    env_fair1_done = 0;
end

always @(posedge i_clk)
begin
    reg_ready = i_ready;
    reg_grant0 = controllable_grant0;
    reg_grant1 = controllable_grant1;
    reg_grant2 = controllable_grant2;

    if (sys_fair1_done & sys_fair2_done & sys_fair3_done)
    begin
        sys_fair1_done = 0;
        sys_fair2_done = 0;
        sys_fair3_done = 0;
        fair_cnt = 0;
    end
    else
    begin
        if (env_fair1_done)
        begin
            sys_fair1_done = sys_fair1_done | sys_fair1;
            sys_fair2_done = sys_fair2_done | sys_fair2;
            sys_fair3_done = sys_fair3_done | sys_fair3;
            fair_cnt = fair_cnt + 1;
        end
        else
        begin
            env_fair1_done = env_fair1_done | env_fair1;
        end
    end

end

endmodule

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
input controllable_grant0;
input controllable_grant1;
input controllable_master;
output o_err;

reg reg_ready;
reg reg_grant0;
reg reg_grant1;
reg [3:0] fair_cnt;
reg sys_fair1_done;
reg sys_fair2_done;

wire sys_safety1;
wire sys_safety2;
wire sys_fair1;
wire sys_fair2;
wire fair_err;
wire o_err;

// G . ready -> (grant[i] <-> X(master = i))
assign sys_safety1 = ~( ~(reg_ready) | (reg_grant0 ^~ (~controllable_master)));
assign sys_safety2 = ~( ~(reg_ready) | (reg_grant1 ^~ controllable_master));

assign sys_fair1 = ( (~controllable_master) | (~i_req0) );
assign sys_fair2 = ( controllable_master | (~i_req1) );

assign fair_err = fair_cnt >= 4'b1000;

assign o_err = sys_safety1 | sys_safety2 | fair_err;

initial
begin
    reg_ready = 0;
    reg_grant0 = 0;
    reg_grant1 = 0;
    fair_cnt = 0;
    sys_fair1_done = 0;
    sys_fair2_done = 0;
end

always @(posedge i_clk)
begin
    reg_ready = i_ready;
    reg_grant0 = controllable_grant0;
    reg_grant1 = controllable_grant1;

    if (sys_fair1_done & sys_fair2_done)
    begin
        sys_fair1_done = 0;
        sys_fair2_done = 0;
    end
    else
    begin
        if ((~sys_fair1_done & sys_fair1) | (~sys_fair2_done & sys_fair2))
        begin
            sys_fair1_done = sys_fair1_done | sys_fair1;
            sys_fair2_done = sys_fair2_done | sys_fair2;
            fair_cnt = 0;
        end
        else
        begin
            fair_cnt = fair_cnt + 1;
        end
    end

end

endmodule

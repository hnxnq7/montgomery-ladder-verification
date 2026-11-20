module rtl_smoke;
  timeunit 1ns;
  timeprecision 1ps;
  typedef logic [254:0] word_t;
  localparam logic [511:0] PRIME = (512'd1 << 255) - 512'd19;
  logic clk, reset, start;
  word_t x1, x2, z2, x3, z3;
  wire ready;
  wire [254:0] out_x2, out_z2, out_x3, out_z3;
  word_t expected_x2, expected_z2, expected_x3, expected_z3;
  word_t edges [6];
  logic [31:0] rng;
  int cases_done, ticks_checked, boundaries_checked, resets_checked, busy_starts;
  protected_ladder_accelerator dut (.*);
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Independent modular oracle: no DUT fold/reduce functions or scratch schedule.
  function automatic word_t modp(input logic [511:0] value);
    return word_t'(value % PRIME);
  endfunction
  function automatic word_t addp(input word_t a, b);
    return modp(512'(a) + 512'(b));
  endfunction
  function automatic word_t subp(input word_t a, b);
    return modp(512'(a) + PRIME - 512'(b));
  endfunction
  function automatic word_t mulp(input word_t a, b);
    return modp(512'(a) * 512'(b));
  endfunction

  task automatic reference_step(input word_t ix1, ix2, iz2, ix3, iz3);
    word_t a, b, c, d, aa, bb, e, da, cb, sum, difference;
    a = addp(modp(512'(ix2)), modp(512'(iz2)));
    b = subp(modp(512'(ix2)), modp(512'(iz2)));
    c = addp(modp(512'(ix3)), modp(512'(iz3)));
    d = subp(modp(512'(ix3)), modp(512'(iz3)));
    aa = mulp(a, a);
    bb = mulp(b, b);
    e = subp(aa, bb);
    da = mulp(d, a);
    cb = mulp(c, b);
    sum = addp(da, cb);
    difference = subp(da, cb);
    expected_x2 = mulp(aa, bb);
    expected_z2 = mulp(e, addp(aa, mulp(255'd121665, e)));
    expected_x3 = mulp(sum, sum);
    expected_z3 = mulp(modp(512'(ix1)), mulp(difference, difference));
  endtask

  function automatic word_t next_word;
    logic [255:0] value;
    value = '0;
    for (int i = 0; i < 8; i++) begin
      rng = rng ^ (rng << 13);
      rng = rng ^ (rng >> 17);
      rng = rng ^ (rng << 5);
      value = (value << 32) | 256'(rng);
    end
    return value[254:0];
  endfunction

  task automatic check_boundary(input int phase);
    boundaries_checked++;
    if (dut.state_q.snd !== ~dut.state_q.fst.bank)
      $fatal(1, "Complement invariant: case %0d phase %0d", cases_done, phase);
    if ($countones(dut.state_q) != 8160 + $countones(dut.state_q.fst.phase))
      $fatal(1, "Register Hamming weight: case %0d phase %0d", cases_done, phase);
    if (dut.state_q.fst.phase !== 5'(phase) || ready !== (phase == 18))
      $fatal(1, "Phase/ready: case %0d expected %0d", cases_done, phase);
  endtask

  task automatic check_outputs(input int phase);
    word_t ex2, ez2, ex3, ez3;
    ex2 = (phase >= 14 && phase <= 18) ? expected_x2 : '0;
    ez2 = (phase == 18) ? expected_z2 : '0;
    ex3 = (phase >= 11 && phase <= 18) ? expected_x3 : '0;
    ez3 = (phase >= 13 && phase <= 18) ? expected_z3 : '0;
    if ({out_x2, out_z2, out_x3, out_z3} !== {ex2, ez2, ex3, ez3})
      $fatal(1, "Output mismatch: case %0d phase %0d", cases_done, phase);
  endtask

  task automatic launch(input word_t ix1, ix2, iz2, ix3, iz3);
    reference_step(ix1, ix2, iz2, ix3, iz3);
    @(negedge clk);
    reset = 0; start = 1;
    x1 = ix1; x2 = ix2; z2 = iz2; x3 = ix3; z3 = iz3;
    @(posedge clk); #1;
    check_boundary(0);
    check_outputs(0);
    if (dut.state_q.fst.bank[0] !== ix1 || dut.state_q.fst.bank[1] !== ix2 ||
        dut.state_q.fst.bank[2] !== iz2 || dut.state_q.fst.bank[3] !== ix3 ||
        dut.state_q.fst.bank[4] !== iz3 || dut.state_q.fst.bank[5] !== 255'd121666)
      $fatal(1, "Start operands");
    for (int i = 6; i < 32; i++)
      if (dut.state_q.fst.bank[i] !== '0) $fatal(1, "Start scratch not cleared");
    @(negedge clk); start = 0;
  endtask

  task automatic ticks(input int count);
    for (int i = 1; i <= count; i++) begin
      @(posedge clk); #1;
      ticks_checked++;
      check_boundary(i);
      check_outputs(i);
    end
  endtask

  task automatic finish_case;
    ticks(18);
    repeat (2) begin
      @(posedge clk); #1;
      check_boundary(18);
      check_outputs(18);
    end
    cases_done++;
  endtask

  task automatic reset_and_idle;
    logic [$bits(dut.state_q)-1:0] before_reset;
    @(negedge clk);
    before_reset = dut.state_q;
    reset = 1; start = 1;
    #1;
    if (dut.state_q !== before_reset) $fatal(1, "Reset/start was not synchronous");
    @(posedge clk); #1;
    check_boundary(31);
    check_outputs(31);
    if (dut.state_q.fst.bank !== '0) $fatal(1, "Reset priority/bank clearing");
    resets_checked++;
    @(negedge clk); reset = 0; start = 0;
    repeat (3) begin
      @(posedge clk); #1;
      check_boundary(31);
      check_outputs(31);
      if (dut.state_q.fst.bank !== '0) $fatal(1, "Idle bank changed");
    end
  endtask

  initial begin
    word_t r1, r2, r3, r4, r5;
    reset = 1; start = 0;
    x1 = 0; x2 = 0; z2 = 0; x3 = 0; z3 = 0;
    rng = 32'h1badf00d;
    cases_done = 0; ticks_checked = 0; boundaries_checked = 0;
    resets_checked = 0; busy_starts = 0;
    edges[0] = 0; edges[1] = 1;
    edges[2] = word_t'(PRIME - 1); edges[3] = word_t'(PRIME);
    edges[4] = word_t'(PRIME + 1); edges[5] = '1;
    @(posedge clk); #1;
    check_boundary(31);
    if (dut.state_q.fst.bank !== '0) $fatal(1, "Initial reset");
    reset_and_idle();

    launch(9, 1, 0, 9, 1);
    if ({expected_x2, expected_z2, expected_x3, expected_z3} !==
        {255'd1, 255'd0, 255'd324, 255'd36}) $fatal(1, "Reference known answer");
    finish_case();
    for (int i = 0; i < 6; i++) begin
      launch(edges[i], edges[i], edges[i], edges[i], edges[i]);
      finish_case();
      launch(edges[i], edges[(i+1)%6], edges[(i+2)%6], edges[(i+3)%6], edges[(i+4)%6]);
      finish_case();
    end
    repeat (16) begin
      r1 = next_word(); r2 = next_word(); r3 = next_word();
      r4 = next_word(); r5 = next_word();
      launch(r1, r2, r3, r4, r5);
      finish_case();
    end
    reset_and_idle();

    launch(9, 1, 0, 9, 1);
    ticks(5);
    launch(edges[5], edges[2], edges[4], edges[1], edges[3]);
    busy_starts++;
    finish_case();
    launch(9, 1, 1, 9, 1);
    ticks(7);
    reset_and_idle();
    if (cases_done != 30 || ticks_checked != 552 || resets_checked != 3 || busy_starts != 1)
      $fatal(1, "Coverage counts");
    $display("PASS: %0d completed cases (1 known, 12 edge/mixed, 16 random, 1 busy restart)", cases_done);
    $display("PASS: %0d tick/output checks, %0d complement/HW boundaries, %0d reset/idle checks",
      ticks_checked, boundaries_checked, resets_checked);
    $display("PASS: synchronous reset priority, busy restart, idle hold, ready/output hold; seed=1badf00d");
    $finish;
  end
  initial begin #20000; $fatal(1, "Timeout"); end
endmodule

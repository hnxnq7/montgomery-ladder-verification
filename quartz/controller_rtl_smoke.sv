module controller_rtl_smoke;
  timeunit 1ns;
  timeprecision 1ps;
  typedef logic [254:0] word_t;
  localparam logic [511:0] PRIME = (512'd1 << 255) - 512'd19;
  logic clk, reset, start;
  word_t x1, scalar;
  wire ready;
  wire [254:0] out_affine;
  word_t active_x1, active_scalar, expected_x, expected_z, expected_affine;
  logic [31:0] rng;
  int current_tick, cases_done, ticks_checked, boundaries_checked, resets_checked, busy_restarts;
  protected_ladder_controller dut (.*);

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Independent integer oracle: no DUT folding, reduction, or swap schedule.
  function automatic word_t modp(input logic [511:0] a);
    return word_t'(a % PRIME);
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

  function automatic word_t reference_inverse(input word_t z);
    word_t power, value, exponent;
    power = z;
    value = 1;
    exponent = word_t'(PRIME - 2);
    // Right-to-left exponentiation is independent of the DUT MSB-first loop.
    for (int i = 0; i < 255; i++) begin
      if (exponent[i]) value = mulp(value, power);
      power = mulp(power, power);
    end
    return value;
  endfunction

  task automatic reference_step(input word_t u, a, b, c, d,
                                output word_t xd, zd, xa, za);
    word_t aa, bb, delta, da, cb, sum, difference;
    aa = mulp(addp(a, b), addp(a, b));
    bb = mulp(subp(a, b), subp(a, b));
    delta = subp(aa, bb);
    da = mulp(subp(c, d), addp(a, b));
    cb = mulp(addp(c, d), subp(a, b));
    sum = addp(da, cb);
    difference = subp(da, cb);
    xd = mulp(aa, bb);
    zd = mulp(delta, addp(aa, mulp(255'd121665, delta)));
    xa = mulp(sum, sum);
    za = mulp(u, mulp(difference, difference));
  endtask

  task automatic reference_ladder(input word_t u, k);
    word_t a, b, c, d, xd, zd, xa, za;
    a = 1; b = 0; c = u; d = 1;
    // Branching ladder, with no previous-bit or final-swap state.
    for (int i = 254; i >= 0; i--) begin
      if (k[i]) begin
        reference_step(u, c, d, a, b, xd, zd, xa, za);
        a = xa; b = za; c = xd; d = zd;
      end else begin
        reference_step(u, a, b, c, d, xd, zd, xa, za);
        a = xd; b = zd; c = xa; d = za;
      end
    end
    expected_x = a;
    expected_z = b;
    expected_affine = mulp(a, reference_inverse(b));
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

  task automatic check_storage;
    boundaries_checked++;
    if ($bits(dut.state_q.fst) != dut.CORE_WIDTH || $bits(dut.state_q) != 2 * dut.CORE_WIDTH)
      $fatal(1, "Stored state width");
    if (dut.response_d.stored_pack !== $unsigned(dut.state_q.fst))
      $fatal(1, "Actual Quartz pack differs from native packed layout at tick %0d", current_tick);
    if (dut.state_q.snd !== ~dut.response_d.stored_pack)
      $fatal(1, "Whole-state complement at tick %0d", current_tick);
    if ($countones(dut.state_q) != dut.CORE_WIDTH)
      $fatal(1, "Whole stored-state Hamming weight at tick %0d", current_tick);
  endtask

  task automatic check_boundary(input int n);
    int want_stage, want_index, want_elapsed, want_core, iteration, offset;
    check_storage();
    want_elapsed = 18;
    want_core = 18;
    if (n == 0) begin
      want_stage = 0; want_index = 254; want_elapsed = 0; want_core = 31;
    end else if (n <= 5100) begin
      iteration = (n - 1) / 20;
      offset = (n - 1) % 20 + 1;
      want_index = 254 - iteration;
      if (offset <= 18) begin
        want_stage = 1; want_elapsed = offset - 1; want_core = offset - 1;
      end else if (offset == 19) want_stage = 2;
      else if (iteration == 254) want_stage = 3;
      else begin want_stage = 0; want_index--; end
      if (dut.state_q.fst.fst.prev !== active_scalar[254 - iteration])
        $fatal(1, "Selected scalar bit at tick %0d", n);
    end else if (n == 5101) begin
      want_stage = 4; want_index = 254;
      if (dut.state_q.fst.fst.x2 !== expected_x || dut.state_q.fst.fst.z2 !== expected_z)
        $fatal(1, "Final projective swap mismatch");
    end else if (n <= 5611) begin
      offset = n - 5101;
      if (offset % 2 == 1) begin
        want_stage = 5; want_index = 254 - (offset - 1) / 2;
      end else if (offset == 510) begin want_stage = 6; want_index = 0; end
      else begin want_stage = 4; want_index = 254 - offset / 2; end
    end else begin want_stage = 7; want_index = 0; end
    if (dut.state_q.fst.fst.stage !== 4'(want_stage) ||
        dut.state_q.fst.fst.index !== 8'(want_index) ||
        dut.state_q.fst.fst.elapsed !== 5'(want_elapsed) || dut.state_q.fst.snd.phase !== 5'(want_core))
      $fatal(1, "Public control mismatch case %0d tick %0d", cases_done, n);
    if (dut.state_q.fst.fst.x1 !== active_x1 || dut.state_q.fst.fst.scalar !== active_scalar)
      $fatal(1, "Request not preserved at tick %0d", n);
    if (ready !== (n == 5612)) $fatal(1, "Ready schedule at tick %0d", n);
    if (out_affine !== ((n == 5612) ? expected_affine : 255'd0))
      $fatal(1, "Affine/gating mismatch case %0d tick %0d", cases_done, n);
    if (n == 5612 && 512'(out_affine) >= PRIME) $fatal(1, "Noncanonical affine output");
  endtask

  task automatic launch(input word_t u, k);
    if (512'(u) >= PRIME) $fatal(1, "Oracle test requires canonical x1");
    reference_ladder(u, k);
    if (u == 9 && k == 0 && expected_affine !== 0) $fatal(1, "Zero scalar oracle");
    if (u == 9 && k == 1 && expected_affine !== 9) $fatal(1, "Unit scalar oracle");
    @(negedge clk);
    reset = 0; start = 1; x1 = u; scalar = k;
    active_x1 = u; active_scalar = k; current_tick = 0;
    @(posedge clk); #1;
    check_boundary(0);
    if (dut.state_q.fst.snd.bank !== '0 || dut.state_q.fst.fst.acc !== 255'd1)
      $fatal(1, "Start did not clear scratch and initialize accumulator");
    @(negedge clk);
    start = 0; x1 = ~u; scalar = ~k;
  endtask

  task automatic ticks_until(input int last);
    while (current_tick < last) begin
      @(posedge clk); #1;
      current_tick++; ticks_checked++;
      check_boundary(current_tick);
    end
  endtask

  task automatic finish_case;
    logic [$bits(dut.state_q)-1:0] before_hold;
    ticks_until(5612);
    before_hold = dut.state_q;
    repeat (3) begin
      @(posedge clk); #1;
      check_boundary(5612);
      if (dut.state_q !== before_hold) $fatal(1, "Done state changed");
    end
    cases_done++;
  endtask

  task automatic check_idle;
    check_storage();
    if (dut.state_q.fst.fst.stage !== 4'd15 || dut.state_q.fst.snd.phase !== 5'd31)
      $fatal(1, "Reset/idle phase");
    // These nine public ones account for every nonzero core bit after reset.
    if ($countones(dut.state_q.fst) != 9 || ready !== 0 || out_affine !== 0)
      $fatal(1, "Reset clearing or idle output gating");
  endtask

  task automatic reset_and_idle;
    logic [$bits(dut.state_q)-1:0] before_edge, idle_snapshot;
    @(negedge clk);
    before_edge = dut.state_q; reset = 1; start = 1;
    #1;
    if (dut.state_q !== before_edge) $fatal(1, "Reset/start not synchronous");
    @(posedge clk); #1;
    check_idle(); resets_checked++;
    idle_snapshot = dut.state_q;
    @(negedge clk); reset = 0; start = 0;
    repeat (3) begin
      @(posedge clk); #1;
      check_idle();
      if (dut.state_q !== idle_snapshot) $fatal(1, "Idle state changed");
    end
  endtask

  initial begin
    word_t u, k;
    reset = 1; start = 0; x1 = 0; scalar = 0;
    rng = 32'h51a7c0de;
    current_tick = 0; cases_done = 0; ticks_checked = 0;
    boundaries_checked = 0; resets_checked = 0; busy_restarts = 0;
    @(posedge clk); #1; check_idle();
    reset_and_idle();
    launch(9, 0); finish_case();
    launch(9, 1); finish_case();
    launch(9, 2); finish_case();
    launch(9, 255'd1 << 254); finish_case();
    launch(9, '1); finish_case();
    launch(0, 7); finish_case();
    launch(word_t'(PRIME - 1), (255'd1 << 200) | 255'd3); finish_case();
    u = modp(512'(next_word())); k = next_word(); launch(u, k); finish_case();
    launch(9, 7); ticks_until(40);
    launch(9, 1); busy_restarts++; finish_case();
    launch(9, 5); ticks_until(5200);
    launch(word_t'(PRIME - 1), 0); busy_restarts++; finish_case();
    launch(9, 4); ticks_until(7); reset_and_idle();
    launch(9, 4); ticks_until(5201); reset_and_idle();
    if (cases_done != 10 || ticks_checked != 66568 || resets_checked != 3 || busy_restarts != 2)
      $fatal(1, "Coverage counts");
    $display("PASS: %0d full 5612-clock cases; independent branching ladder and modular power oracle", cases_done);
    $display("PASS: %0d tick/gating/control checks; %0d whole-pack/complement/HW boundaries", ticks_checked, boundaries_checked);
    $display("PASS: %0d reset/idle checks, %0d busy restarts, projective and affine interruptions, done hold", resets_checked, busy_restarts);
    $display("Stored-state model only; no synthesis timing or physical leakage claim. Seed=51a7c0de");
    $finish;
  end
  initial begin #2000000; $fatal(1, "Timeout"); end
endmodule

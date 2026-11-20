module masked_controller_rtl_smoke;
  timeunit 1ns;
  timeprecision 1ps;
  localparam int K = `QUARTZ_SHARES;
  localparam int GROUPS = 282;
  localparam int BANK_BITS = GROUPS * K * 255;
  localparam int STATE_BITS = BANK_BITS + 16;
  localparam int MATRIX_BITS = K * K * 255;
  localparam int COIN_BITS = GROUPS * (K-1) * 255;
  localparam int RANDOM_BITS = MATRIX_BITS + COIN_BITS;
  localparam int REQUEST_BITS = STATE_BITS + 512 + RANDOM_BITS;
  localparam int WORK_EDGES = 8679;
  localparam logic [511:0] PRIME = (512'd1 << 255) - 512'd19;
  typedef logic [254:0] word_t;
  typedef logic [K-1:0][254:0] shares_t;
  typedef logic [GROUPS-1:0][K-1:0][254:0] bank_t;
  logic clk = 0, reset = 0, start = 0;
  word_t xp = 0, scalar = 0;
  logic [K-1:0][K-1:0][254:0] masks = '0;
  logic [GROUPS-1:0][K-2:0][254:0] coins = '0;
  wire ready;
  wire [K-1:0][254:0] shared_output;
  masked_controller_shell #(.K(K)) dut (.*);

  word_t active_xp, active_scalar, expected_affine;
  word_t ref_x2[0:255], ref_z2[0:255], ref_x3[0:255], ref_z3[0:255];
  logic [31:0] rng = 32'h51a7c0de;
  int phase = 0, index = 0, pc = 0, current_tick = 0, cases_done = 0;
  int resets_checked = 0, busy_starts = 0, projective_checks = 0;
  int idle_edges = 0, done_edges = 0;
  longint unsigned edges = 0, observations = 0, canonical_checks = 0, refresh_groups = 0;
  logic [6:0] phases_seen = '0;

  // Sentinels proved in masked_controller_layout_tests.v; layout checks, not circuit runs.
  task automatic check_layout_sentinels;
    logic [1:0][7:0] bytes;
    logic [15:0] pair_packet;
    bank_t bank;
    logic [K-1:0][K-1:0][254:0] matrix;
    logic [GROUPS-1:0][K-2:0][254:0] refresh;
    shares_t output_words;
    logic [STATE_BITS-1:0] state_packet;
    logic [REQUEST_BITS-1:0] request_packet;
    logic [STATE_BITS+1+K*255-1:0] response_packet;
    bytes[0] = 8'h12; bytes[1] = 8'h34; pair_packet = {8'h12, 8'h34};
    if (bytes !== 16'h3412 || pair_packet !== 16'h1234) $fatal(1, "Quartz array/Pair sentinels");
    bank = '0; matrix = '0; refresh = '0; output_words = '0;
    bank[0][0] = 255'h12; bank[GROUPS-1][K-1] = 255'h34;
    matrix[0][0] = 255'h56; matrix[K-1][K-1] = 255'h78;
    refresh[0][0] = 255'h9a; refresh[GROUPS-1][K-2] = 255'hbc;
    output_words[0] = 255'hde; output_words[K-1] = 255'hf0;
    state_packet = {3'd3, 8'd165, 5'd17, bank};
    if (state_packet[BANK_BITS +: 16] !== 16'd29873 || state_packet[0 +: 255] !== 255'h12 ||
        state_packet[BANK_BITS-255 +: 255] !== 255'h34) $fatal(1, "Quartz state packing");
    request_packet = {state_packet, {1'b1, {1'b0, {255'h123, 255'h456}}}, {matrix, refresh}};
    if (request_packet[0 +: 255] !== 255'h9a || request_packet[COIN_BITS-255 +: 255] !== 255'hbc ||
        request_packet[COIN_BITS +: 255] !== 255'h56 || request_packet[RANDOM_BITS-255 +: 255] !== 255'h78 ||
        request_packet[RANDOM_BITS +: 255] !== 255'h456 || request_packet[RANDOM_BITS+255 +: 255] !== 255'h123 ||
        request_packet[RANDOM_BITS+510 +: 2] !== 2'b10 ||
        request_packet[RANDOM_BITS+512 +: STATE_BITS] !== state_packet)
      $fatal(1, "Quartz nested request/randomness packing");
    response_packet = {state_packet, 1'b1, output_words};
    if (response_packet[0 +: 255] !== 255'hde || response_packet[(K-1)*255 +: 255] !== 255'hf0 ||
        response_packet[K*255] !== 1'b1 || response_packet[K*255+1 +: STATE_BITS] !== state_packet)
      $fatal(1, "Quartz nested response packing");
  endtask

  // Independent integer reduction and branching ladder, not the DUT microprogram.
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
  function automatic word_t reconstruct(input shares_t a);
    word_t value;
    value = 0;
    for (int j = 0; j < K; j++) value = addp(value, a[j]);
    return value;
  endfunction
  function automatic word_t reference_inverse(input word_t z);
    word_t power, value, exponent;
    power = z; value = 1; exponent = word_t'(PRIME - 2);
    // Right-to-left, unlike the controller's MSB-first exponentiation.
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
    sum = addp(da, cb); difference = subp(da, cb);
    xd = mulp(aa, bb);
    zd = mulp(delta, addp(aa, mulp(255'd121665, delta)));
    xa = mulp(sum, sum); za = mulp(u, mulp(difference, difference));
  endtask
  task automatic reference_ladder(input word_t u, k);
    word_t a, b, c, d, xd, zd, xa, za;
    int completed;
    a = 1; b = 0; c = u; d = 1;
    ref_x2[0] = a; ref_z2[0] = b; ref_x3[0] = c; ref_z3[0] = d;
    for (int i = 254; i >= 0; i--) begin
      if (k[i]) begin
        reference_step(u, c, d, a, b, xd, zd, xa, za);
        a = xa; b = za; c = xd; d = zd;
      end else begin
        reference_step(u, a, b, c, d, xd, zd, xa, za);
        a = xd; b = zd; c = xa; d = za;
      end
      completed = 255 - i;
      ref_x2[completed] = a; ref_z2[completed] = b;
      ref_x3[completed] = c; ref_z3[completed] = d;
    end
    expected_affine = mulp(a, reference_inverse(b));
    if (k == 0 && expected_affine !== 0) $fatal(1, "Zero-scalar oracle");
    if (u == 9 && k == 1 && expected_affine !== 9) $fatal(1, "Unit-scalar oracle");
  endtask

  // Reproducible fresh test draws, not an implementation of ideal randomness.
  function automatic word_t random_canonical();
    logic [255:0] value;
    do begin
      for (int j = 0; j < 8; j++) begin
        rng = rng ^ (rng << 13); rng = rng ^ (rng >> 17); rng = rng ^ (rng << 5);
        value[j*32 +: 32] = rng;
      end
    end while (512'(value[254:0]) >= PRIME);
    return value[254:0];
  endfunction
  task automatic fresh_randomness;
    for (int i = 0; i < K; i++)
      for (int j = 0; j < K; j++) masks[i][j] = random_canonical();
    for (int g = 0; g < GROUPS; g++)
      for (int j = 0; j < K-1; j++) coins[g][j] = random_canonical();
  endtask

  task automatic check_storage;
    bank_t bank;
    int hw;
    bank = bank_t'(dut.state_q[BANK_BITS-1:0]);
    if ($bits(dut.state_q) != STATE_BITS || $bits(dut.response_d) != STATE_BITS + 1 + K*255)
      $fatal(1, "Packed width mismatch K=%0d", K);
    if ($isunknown(dut.state_q)) $fatal(1, "Unknown stored bit at edge %0d", edges);
    // Quartz unsigned_app places its first argument low: arrays low-first, Pair fst high.
    if (dut.state_q[BANK_BITS +: 16] !== {3'(phase), 8'(index), 5'(pc)})
      $fatal(1, "Control mismatch edge=%0d wanted=(%0d,%0d,%0d)", edges, phase, index, pc);
    hw = $countones(3'(phase)) + $countones(8'(index)) + $countones(5'(pc));
    for (int g = 0; g < GROUPS; g++) begin
      for (int j = 0; j < K; j++) begin
        if (512'(bank[g][j]) >= PRIME) $fatal(1, "Noncanonical bank edge=%0d group=%0d share=%0d", edges, g, j);
        if (bank[g][j] !== dut.state_q[(g*K+j)*255 +: 255]) $fatal(1, "Word layout mismatch");
        hw += $countones(bank[g][j]); canonical_checks++;
      end
    end
    if (hw != $countones(dut.state_q) || hw > STATE_BITS) $fatal(1, "Full stored-state HW coverage");
    observations++; phases_seen[phase] = 1;
  endtask

  task automatic check_ports;
    bank_t bank;
    bank = bank_t'(dut.state_q[BANK_BITS-1:0]);
    if (ready !== (phase == 6)) $fatal(1, "Current-state ready mismatch edge=%0d", edges);
    if (phase == 6) begin
      if (shared_output !== bank[263]) $fatal(1, "Output is not the current full sharing");
      if (reconstruct(shared_output) !== expected_affine) $fatal(1, "Affine oracle mismatch case=%0d", cases_done);
    end else if (shared_output !== '0) $fatal(1, "Output released before ready");
  endtask

  task automatic check_coordinates(input bank_t bank, input int completed, input logic swapped);
    word_t a, b, c, d;
    a = swapped ? ref_x3[completed] : ref_x2[completed];
    b = swapped ? ref_z3[completed] : ref_z2[completed];
    c = swapped ? ref_x2[completed] : ref_x3[completed];
    d = swapped ? ref_z2[completed] : ref_z3[completed];
    if (reconstruct(bank[255]) !== active_xp || reconstruct(bank[256]) !== a ||
        reconstruct(bank[257]) !== b || reconstruct(bank[258]) !== c || reconstruct(bank[259]) !== d)
      $fatal(1, "Branching oracle coordinates edge=%0d completed=%0d", edges, completed);
    for (int j = 0; j < 255; j++)
      if (reconstruct(bank[j]) !== word_t'(active_scalar[j])) $fatal(1, "Stored scalar bit %0d", j);
    projective_checks++;
  endtask

  task automatic clock_edge(input logic reset_flag, start_flag);
    logic [STATE_BITS-1:0] before_state;
    bank_t before_bank, after_bank;
    word_t base_head, expected_value, expected_tail;
    logic loading, holding;
    int old_phase, old_index, old_pc;
    old_phase = phase; old_index = index; old_pc = pc;
    before_state = dut.state_q;
    before_bank = bank_t'(before_state[BANK_BITS-1:0]);
    loading = !reset_flag && start_flag && (phase == 0 || phase == 6);
    holding = !reset_flag && !loading && (phase == 0 || phase == 6);
    reset = reset_flag; start = start_flag; fresh_randomness();
    #1;
    if (dut.state_q !== before_state) $fatal(1, "State changed without clock");
    check_ports();
    if (reset_flag) begin phase = 0; index = 0; pc = 0; current_tick = 0; resets_checked++; end
    else if (loading) begin
      active_xp = modp(512'(xp)); active_scalar = scalar;
      reference_ladder(active_xp, active_scalar);
      phase = 1; index = 254; pc = 0; current_tick = 0;
    end else if (phase == 1) begin
      if (pc == 31) begin pc = 0; if (index == 0) phase = 2; else index--; end
      else pc++;
    end else if (phase == 2) begin
      if (pc == 7) begin phase = 3; index = 254; pc = 0; end else pc++;
    end else if (phase == 3) phase = 4;
    else if (phase == 4) begin
      if (index == 0) phase = 5; else begin index--; phase = 3; end
    end else if (phase == 5) phase = 6;
    if (!reset_flag && !loading && old_phase > 0 && old_phase < 6) begin
      current_tick++;
      if (start_flag) busy_starts++;
    end
    clk = 1; #1; edges++;
    if (edges > 60000) $fatal(1, "Edge budget exceeded");
    after_bank = bank_t'(dut.state_q[BANK_BITS-1:0]);
    check_storage(); check_ports();
    for (int g = 0; g < GROUPS; g++) begin
      // Scalar bits and xP are unchanged by every busy instruction.
      if (reset_flag || loading || holding || g < 256) begin
        if (reset_flag) expected_value = 0;
        else if (holding) expected_value = reconstruct(before_bank[g]);
        else if (g < 255) expected_value = word_t'(active_scalar[g]);
        else case (g)
          255, 258: expected_value = active_xp;
          256, 259, 263: expected_value = 1;
          default: expected_value = 0;
        endcase
        base_head = (!reset_flag && !loading) ? before_bank[g][0] : expected_value;
        for (int j = 1; j < K; j++) begin
          expected_tail = addp((!reset_flag && !loading) ? before_bank[g][j] : word_t'(0), coins[g][j-1]);
          if (after_bank[g][j] !== expected_tail) $fatal(1, "Refresh tail edge=%0d group=%0d share=%0d", edges, g, j);
          base_head = subp(base_head, coins[g][j-1]);
        end
        if (after_bank[g][0] !== base_head || reconstruct(after_bank[g]) !== expected_value)
          $fatal(1, "Refresh head/reconstruction edge=%0d group=%0d", edges, g);
        refresh_groups++;
      end
    end
    if (holding && old_phase == 0) idle_edges++;
    if (holding && old_phase == 6) done_edges++;
    if (loading) check_coordinates(after_bank, 0, 0);
    if (!reset_flag && old_phase == 1 && old_pc == 31) begin
      check_coordinates(after_bank, 255-old_index, active_scalar[old_index]);
      if (reconstruct(after_bank[260]) !== word_t'(active_scalar[old_index])) $fatal(1, "Previous-bit register");
    end
    if (!reset_flag && old_phase == 2 && old_pc == 7) check_coordinates(after_bank, 255, 0);
    if (!reset_flag && phase == 6 && current_tick != WORK_EDGES) $fatal(1, "Completion edge count");
    clk = 0; #1;
  endtask

  task automatic full_run(input word_t u, k);
    longint unsigned first_edge;
    first_edge = edges; xp = u; scalar = k; clock_edge(0, 1);
    for (int i = 1; i <= WORK_EDGES; i++) begin
      // Changed requests during execution must not restart or replace the request.
      xp = ~u; scalar = ~k;
      clock_edge(0, i == 7 || i == 8169);
    end
    if (edges - first_edge != 8680 || ready !== 1) $fatal(1, "Full-run schedule");
    repeat (3) clock_edge(0, 0);
    cases_done++;
  endtask

  initial begin
    if (K < 2) $fatal(1, "This bench requires at least two shares");
    check_layout_sentinels();
    #1;
    if (dut.state_q !== '0) $fatal(1, "Required public all-zero initial storage");
    check_storage(); check_ports();
    clock_edge(1, 1); repeat (3) clock_edge(0, 0);
    xp = 9; scalar = 7; clock_edge(0, 1);
    repeat (40) clock_edge(0, 0);
    clock_edge(1, 1); repeat (2) clock_edge(0, 0);
    full_run(9, 0);
    full_run(9, 1);
    full_run(9, '1);
    full_run(0, 37);
    clock_edge(1, 1); clock_edge(0, 0);
    // Interrupt affine conversion, including reset priority over start in a busy phase.
    xp = word_t'(PRIME + 3); scalar = 255'd1 << 254; clock_edge(0, 1);
    repeat (8200) clock_edge(0, 0);
    clock_edge(1, 1); repeat (3) clock_edge(0, 0);
    if (cases_done != 4 || resets_checked != 4 || busy_starts != 8 ||
        idle_edges != 9 || done_edges != 12 || phases_seen !== 7'h7f ||
        observations != edges + 1 || canonical_checks != observations * GROUPS * K)
      $fatal(1, "Coverage counts");
    $display("PASS K=%0d full_runs=%0d edges=%0d observations=%0d canonical_words=%0d",
      K, cases_done, edges, observations, canonical_checks);
    $display("PASS full packed HW coverage; branching/power oracle; coordinates=%0d refreshed_groups=%0d",
      projective_checks, refresh_groups);
    $display("PASS synchronous reset/idle, ignored busy starts, done refresh/retention, current-state gating");
    $display("Deterministic test coins; stored-state checks only, not a physical leakage or randomness proof.");
    $display("No raw-input, mask-matrix, or bus leakage claim.");
    $finish;
  end
  initial begin #500000; $fatal(1, "Simulation-time watchdog"); end
endmodule

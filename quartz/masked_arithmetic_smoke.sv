// Combinational regression harness, not a clocked masked-state security model.
module masked_arithmetic_smoke;
  localparam int K = `QUARTZ_SHARES;
  localparam bit [254:0] P = 255'h7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
  typedef bit [K-1:0][254:0] shares_t;
  typedef bit [K-1:0][K-1:0][254:0] matrix_t;
  typedef bit [K-2:0][254:0] coins_t;

  shares_t a, b, sum, difference, product, refreshed, previous_product, previous_refresh;
  matrix_t masks;
  coins_t coins;
  int checks = 0;

  function automatic bit [254:0] addp(input bit [254:0] x, y);
    bit [511:0] wide;
    wide = 512'(x) + 512'(y);
    return 255'(wide % 512'(P));
  endfunction

  function automatic bit [254:0] subp(input bit [254:0] x, y);
    bit [511:0] wide;
    wide = 512'(x) + 2 * 512'(P) - 512'(y);
    return 255'(wide % 512'(P));
  endfunction

  function automatic bit [254:0] mulp(input bit [254:0] x, y);
    bit [511:0] wide;
    wide = 512'(x) * 512'(y);
    return 255'(wide % 512'(P));
  endfunction

  function automatic bit [254:0] random_word();
    bit [255:0] wide;
    for (int i = 0; i < 8; i++) wide[32*i +: 32] = $urandom;
    return wide[254:0];
  endfunction

  function automatic bit [254:0] reconstruct(input shares_t values);
    bit [254:0] result = 0;
    for (int i = 0; i < K; i++) result = addp(result, values[i]);
    return result;
  endfunction

  task automatic verify(input int case_id);
    bit [254:0] expected_product, expected_refresh, cross_value;
    {sum, difference, product, refreshed} = `QUARTZ_ENTRY({a, {b, {masks, coins}}});
    for (int i = 0; i < K; i++) begin
      // Row-wise closed formula, independently of the circuit's sequential pair-update order.
      expected_product = mulp(a[i], b[i]);
      for (int j = 0; j < K; j++) begin
        if (i < j) expected_product = subp(expected_product, masks[i][j]);
        if (j < i) begin
          cross_value = addp(mulp(a[j], b[i]), mulp(a[i], b[j]));
          expected_product = addp(expected_product, addp(masks[j][i], cross_value));
        end
      end
      if (i == 0) begin
        expected_refresh = addp(a[0], 0);
        for (int j = 0; j < K-1; j++) expected_refresh = subp(expected_refresh, coins[j]);
      end else expected_refresh = addp(a[i], coins[i-1]);
      if (sum[i] != addp(a[i], b[i]) || difference[i] != subp(a[i], b[i]) ||
          product[i] != expected_product || refreshed[i] != expected_refresh)
        $fatal(1, "Share mismatch K=%0d case=%0d share=%0d", K, case_id, i);
      if (sum[i] >= P || difference[i] >= P || product[i] >= P || refreshed[i] >= P)
        $fatal(1, "Noncanonical result K=%0d case=%0d share=%0d", K, case_id, i);
    end
    if (reconstruct(sum) != addp(reconstruct(a), reconstruct(b)) ||
        reconstruct(difference) != subp(reconstruct(a), reconstruct(b)) ||
        reconstruct(product) != mulp(reconstruct(a), reconstruct(b)) ||
        reconstruct(refreshed) != reconstruct(a))
      $fatal(1, "Reconstruction mismatch K=%0d case=%0d", K, case_id);
    checks++;
  endtask

  initial begin
    int seed;
    bit [254:0] boundary;
    seed = 32'h13579bdf;
    if (K != 2 && K != 4) $fatal(1, "Harness only covers two and four shares");
    void'($urandom(seed));
    for (int t = 0; t < 64; t++) begin
      for (int i = 0; i < K; i++) begin
        a[i] = random_word();
        b[i] = random_word();
        for (int j = 0; j < K; j++) masks[i][j] = random_word();
      end
      for (int i = 0; i < K-1; i++) coins[i] = random_word();
      if (t < 5) begin
        case (t)
          0: boundary = 0;
          1: boundary = 1;
          2: boundary = P - 1;
          3: boundary = P;
          default: boundary = '1;
        endcase
        for (int i = 0; i < K; i++) begin
          a[i] = boundary;
          b[i] = boundary;
          for (int j = 0; j < K; j++) masks[i][j] = boundary;
        end
        for (int i = 0; i < K-1; i++) coins[i] = boundary;
      end
      if (t == 5) b = a;
      verify(t);
    end

    for (int i = 0; i < K; i++) begin
      a[i] = 255'(32'(i + 2));
      b[i] = 255'(32'(i + 7));
      for (int j = 0; j < K; j++) masks[i][j] = 255'(32'(17 * (i + 1) + j));
    end
    for (int i = 0; i < K-1; i++) coins[i] = 255'(32'(5 * i + 3));
    verify(64);
    previous_product = product;
    previous_refresh = refreshed;
    masks[0][1] = addp(masks[0][1], 1);
    coins[0] = addp(coins[0], 1);
    verify(65);
    if (product == previous_product || refreshed == previous_refresh)
      $fatal(1, "Active mask port did not affect shares K=%0d", K);

    previous_product = product;
    previous_refresh = refreshed;
    for (int i = 0; i < K; i++)
      for (int j = 0; j <= i; j++) masks[i][j] = random_word();
    verify(66);
    if (product != previous_product || refreshed != previous_refresh)
      $fatal(1, "Unused matrix entry affected output K=%0d", K);
    $display("PASS: K=%0d, %0d combinational vectors, exact shares and reconstructions", K, checks);
    $finish;
  end
endmodule

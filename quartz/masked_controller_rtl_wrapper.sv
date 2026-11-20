module masked_controller_shell #(
  parameter int K = `QUARTZ_SHARES
) (
  input logic clk, reset, start,
  input bit [254:0] xp, scalar,
  input bit [K-1:0][K-1:0][254:0] masks,
  input bit [281:0][K-2:0][254:0] coins,
  output wire ready,
  output wire [K-1:0][254:0] shared_output
);
  timeunit 1ns;
  timeprecision 1ps;
  localparam int STATE_BITS = 16 + 282*K*255;
  localparam int OUTPUT_BITS = K*255;
  initial begin
    if (K < 2 || K != `QUARTZ_SHARES)
      $fatal(1, "Share count must match the selected native specialization and be at least two");
  end
  // Requires a platform implementing this public all-zero initial state.
  // Reset is a normal C.tick edge, including fresh whole-bank refresh.
  (* keep = "true", dont_touch = "true" *)
  bit [STATE_BITS-1:0] state_q = '0;
  wire [STATE_BITS+1+OUTPUT_BITS-1:0] response_d;
  assign response_d = `QUARTZ_ENTRY({state_q, {{reset, {start, {xp, scalar}}}, {masks, coins}}});
  always_ff @(posedge clk) state_q <= response_d[OUTPUT_BITS+1 +: STATE_BITS];
  assign ready = response_d[OUTPUT_BITS];
  assign shared_output = response_d[OUTPUT_BITS-1:0];
endmodule

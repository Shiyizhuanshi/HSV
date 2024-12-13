// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
	    input rst,
      input clk,
      input [7:0] in1,
      input [7:0] in2,
      output [15:0] out
      );

  reg [3:0]  stage = 0;
  reg [15:0] accumulator = 0;
  reg [7:0]  in1_shifted = 0;
  reg [15:0] in2_shifted = 0;


  // Logic for controlling the stage
  always @(posedge clk) 
    if (rst || stage == 9)
      stage <= 0;
    else
      stage <= stage + 1;
   
  // Logic for in1_shifted and in2_shifted
  always @(posedge clk) 
    if (rst) begin
	    in1_shifted <= 0;
	    in2_shifted <= 0;
    end 
    else if (stage == 0) begin
      in1_shifted <= in1;
      in2_shifted <= in2;
    end
    else begin
      in1_shifted <= in1_shifted >> 1;
      in2_shifted <= in2_shifted << 1;
    end

  // Logic for the accumulator
  always @(posedge clk)
    if (rst || stage == 9) begin
	    accumulator <= 0;
    end
    else if (in1_shifted[0]) begin
      accumulator <= accumulator + in2_shifted;
    end

  // Output logic
  assign out = accumulator;


  // don't run this as it is, it will take 20 min to run, comment out the properties and keep only necessary ones
  `ifdef FORMAL
    reg [7:0] in1_init;
    reg [7:0] in2_init;
    always @(posedge clk) begin
      if (rst) begin
        in1_init = 0;
        in2_init = 0;
      end
      else if (stage == 0) begin
        in1_init = in1;
        in2_init = in2;
      end
    end

    /*
    #1. Devise a tight upper bound on the value in out, and prove that out never exceeds this bound.
    Refines: out <= 65025
     */
      assert property (@(posedge clk)
          out <= 65025);
        
    // /*
    // #2. Prove that stage increments on each clock cycle.
    // Refines: during calculation, stage increments on each clock cycle except when going to stage 0
    // */
      assert property (@(posedge clk)
          stage != 0 |-> stage == $past(stage) + 1);

    /* 
    #3. Prove the main property: that if the multiplier is in stage 0 and in1 holds
    value x and in2 holds value y, then 9 cycles later the value of out will be
    equal to x * y
    */
      assert property (@(posedge clk)
        disable iff (rst)
          stage == 0 |-> ##9 out == $past(in1, 9) * $past(in2, 9));

    /*
    #4. Prove that the value in out monotonically increases during the computation.
    Refines: during calculation, out increases or stays constant on each clock cycle except when going to stage 0 or resetting
    */
      assert property (@(posedge clk)
          disable iff (rst)
          stage != 0 |-> out >= $past(out));

    /*
    #5. Prove that in the fourth stage of computation, accumulator holds the
    initial value of in2 multiplied by the lowest 4 bits of the initial value of
    in1.
    Refines: in the fourth stage of computation, accumulator holds the
    initial value of in2 multiplied by the lowest 3 bits of the initial value of
    in1. except when resetting
    */
      assert property (@(posedge clk)
          disable iff (rst)
          stage == 4 |-> accumulator == in1_init[2:0] * in2_init);

    /*
    #6. Prove similar properties about the value of the accumulator in the other
    stages
    */
      assert property (@(posedge clk)
          disable iff (rst) (stage == 1 |-> accumulator == 0));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 2 |-> accumulator == in1_init[0:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 3 |-> accumulator == in1_init[1:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 5 |-> accumulator == in1_init[3:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 6 |-> accumulator == in1_init[4:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 7 |-> accumulator == in1_init[5:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 8 |-> accumulator == in1_init[6:0] * in2_init));

      assert property (@(posedge clk)
          disable iff (rst) (stage == 9 |-> accumulator == in1_init[7:0] * in2_init));

    /*
    #7. Prove that in1_shifted always holds the initial value of in1, shifted
    right by stage bits.
    Refines: Prove that in1_shifted always holds the initial value of in1, shifted
    right by (stage-1) bits, when not resetting and not in stage 0
    */
      assert property (@(posedge clk)
          disable iff (rst)
          stage != 0 |-> in1_shifted == in1_init >> (stage-1));

    /*
    #8 Prove that in2_shifted always holds the initial value of in2, shifted
    left by stage bits.
    Refines: Prove that in2_shifted always holds the initial value of in2, shifted
    left by (stage-1) bits. when not resetting and not in stage 0
    */
      assert property (@(posedge clk)
          disable iff (rst)
          stage != 0 |-> in2_shifted == in2_init << (stage-1));

    /*
    #9. Use a cover statement to prove that 13 is a prime number.
    */
      cover property (@(posedge clk)
          (13 % 2 != 0) &&
          (13 % 3 != 0) &&
          (13 % 4 != 0) &&
          (13 % 5 != 0) &&
          (13 % 6 != 0) &&
          (13 % 7 != 0) &&
          (13 % 8 != 0) &&
          (13 % 9 != 0) &&
          (13 % 10 != 0) &&
          (13 % 11 != 0) &&
          (13 % 12 != 0)
          // && (13 % 13 != 0)
      );

      reg [3:0] i;
      reg [3:0] j;
      always @(posedge clk) begin
        for (i = 2; i < 13; i = i + 1) begin
          for (j = 2; j < 13; j = j + 1) begin
              cover property (
                  in1 == i && in2 == j && out != 13
              );
          end
        end
    end
  

    /*
    #10. 
    Can you combine all of the properties you wrote for Questions 5 and 6
    together into a single, concise property?

    SBY 17:22:50 [multiplier] engine_0.basecase: ##   0:09:08  Status: passed
    */

    assert property (@(posedge clk)
        disable iff (rst)
        (stage == 0) ||
        ((stage == 1) && (accumulator == 0)) ||
        ((stage == 2) && (accumulator == in1_init[0:0] * in2_init)) ||
        ((stage == 3) && (accumulator == in1_init[1:0] * in2_init)) ||
        ((stage == 4) && (accumulator == in1_init[2:0] * in2_init)) ||
        ((stage == 5) && (accumulator == in1_init[3:0] * in2_init)) ||
        ((stage == 6) && (accumulator == in1_init[4:0] * in2_init)) ||
        ((stage == 7) && (accumulator == in1_init[5:0] * in2_init)) ||
        ((stage == 8) && (accumulator == in1_init[6:0] * in2_init)) ||
        ((stage == 9) && (accumulator == in1_init[7:0] * in2_init))
    );

  `endif
   
   
endmodule

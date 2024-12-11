// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
		   input 	 rst,
                   input 	 clk,
                   input [7:0] 	 in1,
                   input [7:0] 	 in2,
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
     end else if (stage == 0) begin
        in1_shifted <= in1;
        in2_shifted <= in2;
     end else begin
        in1_shifted <= in1_shifted >> 1;
        in2_shifted <= in2_shifted << 1;
     end

   // Logic for the accumulator
   always @(posedge clk)
     if (rst || stage == 9) begin
	accumulator <= 0;
     end else if (in1_shifted[0]) begin
        accumulator <= accumulator + in2_shifted;
     end

   // Output logic
   assign out = accumulator;


`ifdef FORMAL
  
  // Task1: Devise a tight upper bound on the value in out, 
  //        and prove that out never exceeds this bound.
  property upperboud;
    out <= 65025;
  endproperty

  // Task2: Prove that stage increments on each clock cycle
  property stage_increments;
    always @(posedge clk)
    // iff?
      stage < $past(stage);
  endproperty

  // Task3: Prove the main property: that if the multiplier is in stage 0 and in1 holds
  //        value x and in2 holds value y, then 9 cycles later the value of out will be
  //        equal to x × y. [Hint: you can write $past(e,n) to refer to the value of
  //        expression e from n clock cycles ago, where n is an integer constant.]
  property multiplication;
    // always @(posedge clk)
    //   if (stage == 9)
    //     out == in1 * in2;
    //   else
    //     out == $past(out, 1);
    1 == 1;
  endproperty

  // Task4: Prove that the value in out monotonically increases during the computation
  property monotonically_increasing;
    // always @(posedge clk)
    //   if (stage == 0)
    //     out >= $past(out, 1);
    //   else
    //     out == $past(out, 1);
    1 == 1;
  endproperty

  // Task5: Prove that in the fourth stage of computation, accumulator holds the
  //        initial value of in2 multiplied by the lowest 4 bits of the initial value of in1.
  property accumulator_stage_4;
    // always @(posedge clk)
    //   if (stage == 4)
    //     accumulator == in1[3:0] * in2;
    //   else
    //     accumulator == $past(accumulator, 1);
    1 == 1;
  endproperty

  // Task6: Prove similar properties about the value of the accumulator in the other stages.
  property accumulator_stage_0;
    // always @(posedge clk)
    //   if (stage == 0)
    //     accumulator == 0;
    //   else
    //     accumulator == $past(accumulator, 1);
    1 == 1;
  endproperty

  // Task7: Prove that in1_shifted always holds the initial value of in1, shifted right by stage bits.
  property in1_shifted_correct;
    // always @(posedge clk)
    //   if (stage == 0)
    //     in1_shifted == in1;
    //   else
    //     in1_shifted == $past(in1_shifted, 1);
    1 == 1;
  endproperty

  // Task8: Prove that in2_shifted always holds the initial value of in2, shifted left by stage bits.
  property in2_shifted_correct;
    // always @(posedge clk)
    //   if (stage == 0)
    //     in2_shifted == in2;
    //   else
    //     in2_shifted == $past(in2_shifted, 1);
    1 == 1;
  endproperty

  // Task9: Use a cover statement to prove that 13 is a prime number.
  property prime_number;
    // cover (13);
    1 == 1;
  endproperty

  // Task10: Can you combine all of the properties you wrote for Questions 5 and 6 
  //         together into a single, concise property?
  property accumulator_correct;
    // always @(posedge clk)
    //   if (stage == 0)
    //     accumulator == 0;
    //   else if (stage == 4)
    //     accumulator == in1[3:0] * in2;
    //   else
    //     accumulator == $past(accumulator, 1);
    1 == 1;
  endproperty

   always @(posedge clk) begin

   assert (0==0); 
     // write your properties here!

   end

`endif
   
   
endmodule

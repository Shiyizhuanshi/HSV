module counter (
    input clk,
    output reg [5:0] count
);
    initial count = 0;

    always @(posedge clk) begin
        if (count == 15)
            count <= 0;
        else
            count <= count + 1;
    end

    `ifdef FORMAL

    // Define the counter increment behavior as a property
    property going_up;
        (count > 0) |-> (count == $past(count) + 1);
    endproperty

    // Assertions for formal verification
    always @(posedge clk) begin
        // Use assert with the property directly
        assert (count < 32);
        assert property (going_up); // Use the property correctly in an assertion
    end
    `endif

endmodule

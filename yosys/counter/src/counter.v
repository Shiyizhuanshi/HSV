module counter (
    input clk,
    output reg [5:0] count
);
    initial count = 0;

    property going_up;
        @(posedge clk) $rose(count);
        count > 0 |-> count == $past(count) + 1;
    endproperty
    always @(posedge clk) begin
        // assert property (count > 0 | -> count == $past(count) + 1); 
        if (count == 15)
            count <= 0;
        else
            count <= count + 1;
    end

`ifdef FORMAL
    always @(*) begin
        assert (count < 32);
    end
`endif

endmodule

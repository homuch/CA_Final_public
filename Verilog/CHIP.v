// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I
    );
    //==== I/O Declaration ========================
    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    //==== Reg/Wire Declaration ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg

    reg [4:0] state, state_nxt;

    parameter IDLE = 5'd0;
    parameter AUPIC  = 5'd1;
    parameter JAL  = 5'd2;
    parameter JALR = 5'd3;
    parameter BEQ = 5'd4;
    parameter LW  = 5'd5;
    parameter SW  = 5'd6;
    parameter ADDI  = 5'd7;
    parameter SLTI  = 5'd8;
    parameter ADD  = 5'd9;
    parameter SUB  = 5'd10;
    parameter XOR  = 5'd11;
    parameter MUL  = 5'd12;

    //==== Submodule Connection ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: other submodules

    //==== Combinational Part =====================

    assign rs1=mem_rdata_I[19:15];
    assign rs2=mem_rdata_I[24:20];
    assign rd=mem_rdata_I[11:7];

    // Todo: any combinational/sequential circuit

    // decode instruction
    always @(*)begin
        case mem_rdata_I[6:0]
            7'b0010011:begin//imm
                case mem_rdata_I[14:12]:
                    3'b000:begin//addi
                        state_nxt=ADDI;
                    end
                    3'b010:state_nxt=SLTI;//slti
                endcase
            end
            7'b0110011:begin//R-type
                case {mem_rdata_I[31:25],mem_rdata_I[14:12]}:
                    10'd0:state_nxt=ADD;//add
                    10'h100:state_nxt=SUB;//sub
                    10'h4:state_nxt=XOR;//xor
                    10'h8:state_nxt=MUL;//mul
                endcase
            end
            7'b0000011:begin//load
                case mem_rdata_I[14:12]:
                    3b'010:state_nxt=LW;//LW
                endcase
            end
            7'b0100011:begin//save
                case mem_rdata_I[14:12]:
                    3b'010:state_nxt=SW;//SW
                endcase
            end
            7'b1100011:begin//branch
                case mem_rdata_I[14:12]:
                    3b'000:state_nxt=BEQ;//beq
                endcase
            end

            7'b0010111:begin//AUIPC
                state_nxt=AUPIC;
            end
            
            default:state_nxt=IDLE;

        endcase
    end

    //ALU




    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
            state <=IDLE;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'h7fffeffc; // sp: stack pointer
                    32'd3: mem[i] <= 32'h10008000; // gp: global pointer
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2

endmodule
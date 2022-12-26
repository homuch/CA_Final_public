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
    reg   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg

    reg [4:0] state, state_nxt;
    reg [2:0] sub_state, sub_state_nxt;
    reg readInstr,nextReadInstr, updatePC;
    wire branch;
    reg regShouldWrite;

    parameter IDLE = 5'd0;
    parameter AUIPC  = 5'd1;
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

    parameter ID = 3'd0;
    parameter EX = 3'd1;
    parameter MEM = 3'd2;
    parameter WB = 3'd3;
    parameter BUFFER = 3'd4;

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

    assign rs1 = mem_rdata_I[19:15];
    assign rs2 = mem_rdata_I[24:20];
    assign rd = mem_rdata_I[11:7];
    assign mem_addr_I = PC;
    assign mem_addr_D = (state == LW)? rs1_data + mem_rdata_I[31:20]:rs1_data + {mem_rdata_I[31:25],mem_rdata_I[11:7]};
    assign mem_wen_D = (state == SW && sub_state==EX)? 1'd1:1'd0;
    assign mem_wdata_D = rs2_data;
    assign regWrite = regShouldWrite&&(sub_state==WB);

    assign branch = (state==JAL||state==JALR||state==BEQ);
    // Todo: any combinational/sequential circuit

    // decode instruction
    always @(*)begin
        if(!readInstr)begin
            state_nxt = state;
            nextReadInstr = 1'd0;
        end
        else begin
            nextReadInstr=1'd0;
            sub_state_nxt = EX;
            case (mem_rdata_I[6:0])
                7'b0010011:begin//imm
                    case (mem_rdata_I[14:12])
                        3'b000:begin//addi
                            state_nxt = ADDI;
                        end
                        3'b010:state_nxt = SLTI;//slti
                    endcase
                end
                7'b0110011:begin//R-type
                    case ({mem_rdata_I[31:25],mem_rdata_I[14:12]})
                        10'd0:state_nxt=ADD;//add
                        10'h100:state_nxt=SUB;//sub
                        10'h4:state_nxt=XOR;//xor
                        10'h8:state_nxt=MUL;//mul
                    endcase
                end
                7'b0000011:begin//load
                    case (mem_rdata_I[14:12])
                        3'b010:state_nxt=LW;//LW
                    endcase
                end
                7'b0100011:begin//save
                    case (mem_rdata_I[14:12])
                        3'b010:state_nxt=SW;//SW
                    endcase
                end
                7'b1100011:begin//branch
                    case (mem_rdata_I[14:12])
                        3'b000:state_nxt=BEQ;//beq
                    endcase
                end

                7'b0010111:begin//AUIPC
                    state_nxt=AUIPC;
                end

                7'b1101111:begin
                    state_nxt = JAL;
                end

                7'b1100111:begin
                    state_nxt = JALR;
                end
                default:state_nxt=IDLE;
            endcase
        end
    end


    //ALU
    always @(*)begin
        case (sub_state)
            ID:regShouldWrite = 1'd0;
            EX:begin
                rd_data = 32'd0;
                // mem_addr_D=32'd0;
                sub_state_nxt = WB;
                updatePC=1'd0;
                regShouldWrite = 1'd0;
                // mem_wen_D = 1'd0;
                case (state)
                    ADDI:begin
                        rd_data = mem_rdata_I[31:20]+rs1_data;
                    end
                    // SLTI: rd_data = ($signed(rs1_data)<$signed({20{mem_addr_I[31]},mem_addr_I[31:20]}))? 32'd1:32'd0;
                    ADD: rd_data = rs1_data+rs2_data;
                    SUB: rd_data = rs1_data-rs2_data;
                    XOR: rd_data = rs1_data^rs2_data;
                    // MUL://mul
                    LW:begin 
                        // mem_addr_D = rs1_data + mem_rdata_I[31:20];
                        // mem_wen_D = 1'd0;
                    end
                    SW:begin
                        // mem_addr_D = rs1_data + {mem_rdata_I[31:25],mem_rdata_I[11:7]};
                        // mem_wdata_D = rs2_data;
                        // mem_wen_D = 1'd1;
                    end
                    AUIPC:rd_data = {mem_rdata_I[31:12],12'd0} + PC;
                    // BEQ:sub_state_nxt=ID;
                    JAL:rd_data = PC+32'd4;
                    JALR:rd_data = PC+32'd4;
                    default:begin
                        sub_state_nxt = ID;
                        updatePC=1'd1;
                    end
                endcase
            end
            WB:begin
                regShouldWrite = 1'd0;
                sub_state_nxt = BUFFER;
                case (state)
                    ADDI:regShouldWrite = 1'd1;
                    SLTI: regShouldWrite = 1'd1;
                    ADD: regShouldWrite = 1'd1;
                    SUB: regShouldWrite = 1'd1;
                    XOR: regShouldWrite = 1'd1;
                    // MUL://mul
                    LW: begin
                        regShouldWrite = 1'd1;
                        rd_data = mem_rdata_D;
                    end
                    AUIPC:regShouldWrite = 1'd1;
                    JAL:regShouldWrite = 1'd1;
                    JALR:regShouldWrite = 1'd1;
                endcase
            end
            BUFFER:begin
                sub_state_nxt = ID;
                updatePC = 1'd1;
            end
        endcase
    end

    //PC update/branch
    always @(*)begin
        PC_nxt = PC;
        nextReadInstr = 1'd0;
        if(updatePC)begin
            nextReadInstr=1'd1;
            PC_nxt = PC+32'd4;
            if(branch)begin
                if(state==JAL)begin
                    PC_nxt = {mem_rdata_I[31],mem_addr_I[19:12],mem_addr_I[20],mem_addr_I[30:21],1'd0}+PC;
                end
                else if(state==JALR)begin
                    PC_nxt = rs1_data+mem_rdata_I[31:20];
                end
                else if(state==BEQ) begin
                    if(rs1_data==rs2_data)begin
                        PC_nxt = {mem_rdata_I[12],mem_rdata_I[7],mem_rdata_I[30:25],mem_rdata_I[11:8],1'd0}+PC;
                    end
                end            
        end
        end
        updatePC = 1'd0;
    end

    


    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
            state <=IDLE;
            sub_state <=ID;
            readInstr <= 1'd1;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt;
            sub_state<=sub_state_nxt;
            readInstr <=nextReadInstr;
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

// module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
//     // Todo: your HW2

// endmodule
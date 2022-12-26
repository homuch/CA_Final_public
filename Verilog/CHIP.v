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
    reg aluValid, aluMode, in_A,in_B,mulWaiting;
    wire aluReady,aluOut;


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

    mulDiv alu0(
        .clk(clk),
        .rst_n(rst_n),
        .valid(aluValid),
        .ready(aluReady),
        .mode(aluMode),
        .in_A(in_A),
        .in_B(in_B),
        .out(aluOut)
    );

    //==== Combinational Part =====================

    assign rs1 = mem_rdata_I[19:15];
    assign rs2 = mem_rdata_I[24:20];
    assign rd = mem_rdata_I[11:7];
    assign mem_addr_I = PC;
    assign mem_addr_D = (state == LW)? $signed(rs1_data) + $signed(mem_rdata_I[31:20]):$signed(rs1_data) + $signed({mem_rdata_I[31:25],mem_rdata_I[11:7]});
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
        if(state!=MUL)begin
            mulWaiting = 1'd0;
            aluMode = 2'd1;
            aluValid = 1'd0;
            in_A = 32'd0;
            in_B = 32'd0;
        end
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
                        rd_data = $signed(mem_rdata_I[31:20])+$signed(rs1_data);
                    end
                    SLTI:begin
                         rd_data =32'd0;
                         if($signed(rs1_data)<$signed(mem_addr_I[31:20]))begin
                            rd_data = 32'd1;
                         end
                    end
                    ADD: rd_data = $signed(rs1_data)+$signed(rs2_data);
                    SUB: rd_data = $signed(rs1_data)-$signed(rs2_data);
                    XOR: rd_data = rs1_data^rs2_data;
                    MUL:begin
                        if(!mulWaiting)begin
                            aluValid = 1'd1;
                        end
                        else aluValid = 1'd0;

                        in_A = rs1_data;
                        in_B = rs2_data;
                        aluMode = 2'd1;
                        mulWaiting=1'd1;
                        sub_state_nxt = EX;
                        rd_data = aluOut;
                        if(aluReady)begin
                            sub_state_nxt = WB;
                            mulWaiting = 1'd0;
                        end
                    end
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
                    BEQ:rd_data = 32'd0;
                    // default:begin
                    //     sub_state_nxt = ID;
                    //     updatePC=1'd1;
                    // end
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
                    MUL:regShouldWrite = 1'd1;
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
                    PC_nxt = $signed({mem_rdata_I[31],mem_rdata_I[19:12],mem_rdata_I[20],mem_rdata_I[30:21],1'd0})+$signed(PC);
                end
                else if(state==JALR)begin
                    PC_nxt = $signed(rs1_data)+$signed(mem_rdata_I[31:20]);
                end
                else if(state==BEQ) begin
                    if(rs1_data==rs2_data)begin
                        PC_nxt = $signed({mem_rdata_I[12],mem_rdata_I[7],mem_rdata_I[30:25],mem_rdata_I[11:8],1'd0})+$signed(PC);
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

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
        // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: shift, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter SHIFT = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    assign ready = (state == OUT);
    assign out = ready? shreg : 64'd0;
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if(!valid)state_nxt = IDLE;
                else begin
                    case(mode)
                        2'd0 : state_nxt = MUL;
                        2'd1 : state_nxt = DIV;
                        2'd2 : state_nxt = SHIFT;
                        2'd3 : state_nxt = AVG;
                        default: state_nxt = IDLE;
                    endcase
                end
            end
            MUL : state_nxt = counter<31 ? MUL:OUT;
            DIV : state_nxt = counter<31 ? DIV:OUT;
            SHIFT : state_nxt = OUT;
            AVG : state_nxt = OUT;
            OUT : state_nxt = IDLE;
            default : state_nxt = IDLE;
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        if(state == MUL || state == DIV)
            counter_nxt = counter + 5'd1;
        else
            counter_nxt = 5'd0;
    end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*)begin
        // shreg_nxt = shreg;
        case(state)
            MUL : 
                alu_out = shreg[0]? alu_in + shreg[63:32] : shreg[63:32];
                //shreg_nxt[63:32] = alu_out;
            DIV : 
                alu_out = (shreg[62:31] >= alu_in)? {1'd1, shreg[62:31]-alu_in}:{1'd0, shreg[62:31]};//with left shifted
                // shreg_nxt[63:32] = alu_out;shreg_nxt[0] = 1;
            SHIFT :
                alu_out = shreg[31:0]>>alu_in[2:0];
            AVG : // note that alu_out is 33'
                alu_out = (shreg[31:0] + alu_in)>>1;
            default:
                alu_out = 33'd0;
        endcase
    end    
    
    // Todo 4: Shift register
    always @(*)begin
        shreg_nxt = shreg;// avoid latch
        case(state)
            IDLE : begin
                shreg_nxt = 64'd0;
                if(valid) shreg_nxt[31:0] = in_A;
                else ;
            end
            MUL : begin
                //shreg_nxt = {1'd0, shreg_nxt[63:1]};// right shift
                shreg_nxt = shreg>>1;
                shreg_nxt[63:31] = alu_out;
            end
            DIV : begin
                //shreg_nxt = {shreg_nxt[62:0], 1'd0};// left shift
                shreg_nxt = shreg<<1;
                shreg_nxt[63:32]= alu_out[31:0];//discard(left shift) leftmost bit i.e. alu_out[31]
                shreg_nxt[0] = alu_out[32];
            end
            SHIFT : 
                shreg_nxt = {32'd0, alu_out[31:0]};
            AVG : 
                shreg_nxt = {32'd0, alu_out[31:0]};
            default:
                shreg_nxt = 64'd0;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            shreg <=64'd0;
            alu_in <=32'd0;
            counter <= 5'd0;
        end
        else begin
            state <= state_nxt;
            shreg <=shreg_nxt;
            alu_in <=alu_in_nxt;
            counter <= counter_nxt;
        end
    end

endmodule
package computer

fun main() {
    val fileToLoad = "sample/input4.bin"
    val memory = Memory.load(20000000, fileToLoad)

    val logger = initLogger()
    val controlUnit: ControlUnitInterface = ControlUnit(memory, logger)
    val processResult = controlUnit.process()

    logger.printProcessResult(processResult)
}

private fun initLogger() : Logger {
    return PipeLineLogger(loggingSignal)
}

val loggingSignal = LoggingSignal(
    cycle = true,
    cyclePrintPeriod = 1,
    fetch = true,
    decode = true,
    execute = true,
    memoryAccess = true,
    writeBack = true,
    resultInformation = true,
    sleepTime = 0,
    from = 7777,
    to = 8888
)


class And {
    companion object {
        fun and(src1 : Boolean, src2 : Boolean): Boolean {
            return src1 and src2
        }
    }
}
class Latch<T>(
    Value: T
) {
    private var ip = Value
    private var op = Value

    fun fetch(): T {
        return op
    }
    fun store(ip: T) {
        this.ip = ip
    }
    fun flush() {
        this.op = this.ip
    }
}

class Latches {

    private val IF_ID = Latch(FetchResult())
    private val ID_EX = Latch(DecodeResult())
    private val EX_MA = Latch(ExecutionResult())
    private val MA_WB = Latch(MemoryAccessResult())

    fun ifid(ifResult: FetchResult) {
        IF_ID.store(ifResult)
    }
    fun idex(idResult: DecodeResult) {
        ID_EX.store(idResult)
    }
    fun exma(exResult: ExecutionResult) {
        EX_MA.store(exResult)
    }
    fun mawb(maResult: MemoryAccessResult) {
        MA_WB.store(maResult)
    }
    fun ifid(): FetchResult {
        return IF_ID.fetch()
    }
    fun idex(): DecodeResult {
        return ID_EX.fetch()
    }
    fun exma(): ExecutionResult {
        return EX_MA.fetch()
    }
    fun mawb(): MemoryAccessResult {
        return MA_WB.fetch()
    }
    fun flushAll() {
        IF_ID.flush()
        ID_EX.flush()
        EX_MA.flush()
        MA_WB.flush()
    }
}
class Memory(
    size: Int,
    private val memory: Array<Byte> = Array(size) { 0 }
) {

    companion object {
        fun load(size: Int, path: String): Memory {
            DataInputStream(FileInputStream(path)).use { it ->
                val memory: Array<Byte> = Array(size) { 0 }
                val bytes = ByteArray(2048)
                var address = 0
                while (it.read(bytes) > 0) {
                    for(i : Int in bytes.indices step (4)) {
                        memory[address] = bytes[i+3]
                        memory[address+1] = bytes[i+2]
                        memory[address+2] = bytes[i+1]
                        memory[address+3] = bytes[i]
                        address+=4
                    }
                }
                return Memory(size, memory)
            }
        }
    }

    fun read(address: Int, memRead: Boolean = true): Int =
        if (memRead) {
            val i1 = memory[address].toInt() shl 0 and 0x000000FF
            val i2 = memory[address + 1].toInt() shl 8 and 0x0000FF00
            val i3 = memory[address + 2].toInt() shl 16 and 0x00FF0000
            val i4 = memory[address + 3].toInt() shl 24
            i4+ i3 + i2 + i1
        } else 0

    fun write(address: Int, value: Int, memWrite: Boolean = true) {
        if (memWrite) {
            memory[address] = (value and 0xFF).toByte()
            memory[address + 1] = (value shr 8 and 0xFF).toByte()
            memory[address + 2] = (value shr 16 and 0xFF).toByte()
            memory[address + 3] = (value shr 24 and 0xFF).toByte()
        }
    }
}
class Mux {
    companion object {
        fun mux(signal: Boolean, trueResult: Int, falseResult: Int) =
            if (signal)
                trueResult
            else
                falseResult
    }
}

class ControlUnit(
    private val memory: Memory,
    private val logger: Logger
) : ControlUnitInterface {
    private val scoreBoardingRegisters = ScoreBoardingRegisters(32)
    private val decodeUnit = DecodeUnit()
    private val alu = ALUnit()
    private val stallUnit = StallUnit()
    private val dataDependencyUnit = DataDependencyUnit(scoreBoardingRegisters)
    private val latches = Latches()

    override fun process(): Int {
        var cycle = 0
        var validCycle = 0

        var cycleResult = CycleResult()
        val endFlag = EndFlag()

        while (true) {
            logger.printCycle(cycleResult.valid, validCycle)

            endFlag.update(cycleResult.lastInstruction)
            val pc = mux(stallUnit.isMelt, stallUnit.freezePc, cycleResult.nextPc)
            val valid = stallUnit.valid && !endFlag.isEnd

            cycleResult = cycleExecution(valid, pc)

            if (cycleResult.lastCycle) {
                return cycleResult.value
            }

            if (cycleResult.valid) {
                validCycle++
            }

            latches.flushAll()
            stallUnit.next()
            cycle++
        }
    }

    private fun cycleExecution(valid: Boolean, pc: Int): CycleResult {
        val ifResult = fetch(valid, pc)
        latches.ifid(ifResult)

        val idResult = decode(latches.ifid())
        latches.idex(idResult)

        val exResult = execute(latches.idex())
        latches.exma(exResult)

        val maResult = memoryAccess(latches.exma())
        latches.mawb(maResult)

        val wbResult = writeBack(latches.mawb())

        if (idResult.dataHazard) {
            ifResult.valid = false
            idResult.valid = false
            stallUnit.sleep(2, idResult.pc)
        }

        if (exResult.jump) {
            ifResult.valid = false
            idResult.valid = false
            if (exResult.nextPc == -1) {
                exResult.controlSignal.isEnd = true
            }
        }

        logger.log(ifResult, idResult, exResult, maResult, wbResult)

        val nextPc = mux(exResult.jump, exResult.nextPc, pc + 4)
        return CycleResult(
            nextPc = nextPc,
            value = scoreBoardingRegisters[2],
            valid = wbResult.valid,
            lastInstruction = exResult.controlSignal.isEnd,
            lastCycle = wbResult.controlSignal.isEnd
        )
    }

    private fun fetch(valid: Boolean, pc: Int): FetchResult {
        if (!valid) {
            return FetchResult(valid, 0, 0)
        }
        val instruction = memory.read(pc)
        return FetchResult(
            valid = valid && (instruction != 0),
            pc = pc,
            instruction = instruction
        )
    }

    private fun decode(ifResult: FetchResult): DecodeResult {
        if (!ifResult.valid) {
            return DecodeResult(ifResult.valid, 0, false)
        }
        val instruction = decodeUnit.parse(ifResult.pc + 4, ifResult.instruction)
        val dataHazard = dataDependencyUnit.hasHazard(instruction.rs, instruction.rt)

        val valid = and(ifResult.valid, !dataHazard)
        val controlSignal = decodeUnit.controlSignal(valid, instruction.opcode)

        var writeRegister = mux(controlSignal.regDest, instruction.rd, instruction.rt)
        writeRegister = mux(controlSignal.jal, 31, writeRegister)
        scoreBoardingRegisters.book(controlSignal.regWrite, writeRegister, ifResult.pc)

        return DecodeResult(
            valid = valid,
            pc = ifResult.pc,
            dataHazard = dataHazard,
            shiftAmt = instruction.shiftAmt,
            immediate = instruction.immediate,
            address = instruction.address,
            readData1 = scoreBoardingRegisters[instruction.rs],
            readData2 = scoreBoardingRegisters[instruction.rt],
            writeRegister = writeRegister,
            controlSignal = controlSignal
        )
    }

    private fun execute(idResult: DecodeResult): ExecutionResult {
        if (!idResult.valid) {
            return ExecutionResult(controlSignal = idResult.controlSignal)
        }

        val controlSignal = idResult.controlSignal
        var src1 = mux(controlSignal.shift, idResult.readData2, idResult.readData1)
        src1 = mux(controlSignal.upperImm, idResult.immediate, src1)

        var src2 = mux(controlSignal.aluSrc, idResult.immediate, idResult.readData2)
        src2 = mux(controlSignal.shift, idResult.shiftAmt, src2)
        src2 = mux(controlSignal.upperImm, 16, src2)

        val aluResult = alu.operate(
            aluOp = controlSignal.aluOp,
            src1 = src1,
            src2 = src2
        )

        val aluValue = mux(controlSignal.jal, idResult.pc + 8, aluResult.value)

        val branchCondition = and(aluResult.isTrue, controlSignal.branch)
        var nextPc = mux(branchCondition, idResult.immediate, idResult.pc)
        nextPc = mux(controlSignal.jump, idResult.address, nextPc)
        nextPc = mux(controlSignal.jr, idResult.readData1, nextPc)

        return ExecutionResult(
            valid = idResult.valid,
            pc = idResult.pc, // TODO :: only for logging
            aluValue = aluValue,
            memWriteValue = idResult.readData2,
            writeRegister = idResult.writeRegister,
            nextPc = nextPc,
            jump = branchCondition || controlSignal.jump || controlSignal.jr,
            controlSignal = controlSignal
        )
    }

    private fun memoryAccess(exResult: ExecutionResult): MemoryAccessResult {
        if (!exResult.valid) {
            return MemoryAccessResult(controlSignal = exResult.controlSignal)
        }

        val controlSignal = exResult.controlSignal
        val memReadValue = memory.read(
            memRead = controlSignal.memRead,
            address = exResult.aluValue,
        )

        memory.write(
            memWrite = controlSignal.memWrite,
            address = exResult.aluValue,
            value = exResult.memWriteValue
        )

        return MemoryAccessResult(
            valid = exResult.valid,
            pc = exResult.pc, // TODO :: only for logging
            memReadValue = memReadValue,
            memWriteValue = exResult.memWriteValue,
            aluValue = exResult.aluValue,
            writeRegister = exResult.writeRegister,
            controlSignal = controlSignal
        )
    }

    private fun writeBack(maResult: MemoryAccessResult): WriteBackResult {
        if (!maResult.valid) {
            return WriteBackResult(controlSignal = maResult.controlSignal)
        }

        val controlSignal = maResult.controlSignal
        val regWriteValue = mux(controlSignal.memToReg, maResult.memReadValue, maResult.aluValue)

        scoreBoardingRegisters.write(
            regWrite = controlSignal.regWrite,
            writeRegister = maResult.writeRegister,
            writeData = regWriteValue,
            tag = maResult.pc
        )

        return WriteBackResult(
            valid = maResult.valid,
            pc = maResult.pc, // TODO :: only for logging
            writeRegister = maResult.writeRegister,
            regWriteValue = regWriteValue,
            controlSignal = controlSignal,
        )
    }
}
class ControlUnit_SingleCycle(
    private val memory: Memory,
    private val logger: Logger
) : ControlUnitInterface {
    private val registers = Registers(32)
    private val decodeUnit = DecodeUnit()
    private val alu = ALUnit()

    override fun process(): Int {
        var cycle = 0
        var cycleResult = CycleResult()

        while (true) {
            logger.printCycle(cycle)

            val pc = cycleResult.nextPc
            if (pc == -1) {
                return cycleResult.value
            }

            cycleResult = cycleExecution(pc)
            cycle++
        }
    }

    private fun cycleExecution(pc: Int): CycleResult {
        val ifResult = fetch(true, pc)
        val idResult = decode(ifResult)
        val exResult = execute(idResult)
        val maResult = memoryAccess(exResult)
        val wbResult = writeBack(maResult)

        logger.log(ifResult, idResult, exResult, maResult, wbResult)

        val nextPc = mux(exResult.jump, exResult.nextPc, pc+4)
        return CycleResult(
            nextPc = nextPc,
            valid = true,
            value = registers[2]
        )
    }

    private fun fetch(valid: Boolean, pc: Int): FetchResult {
        val instruction = memory.read(pc)
        return FetchResult(true, pc, instruction)
    }

    private fun decode(ifResult: FetchResult): DecodeResult {
        val instruction = decodeUnit.parse(ifResult.pc + 4, ifResult.instruction)
        val controlSignal = decodeUnit.controlSignal(opcode = instruction.opcode)

        var writeRegister = mux(controlSignal.regDest, instruction.rd, instruction.rt)
        writeRegister = mux(controlSignal.jal, 31, writeRegister)

        return DecodeResult(
            valid = true,
            pc = ifResult.pc,
            shiftAmt = instruction.shiftAmt,
            immediate = instruction.immediate,
            address = instruction.address,
            readData1 = registers[instruction.rs],
            readData2 = registers[instruction.rt],
            writeRegister = writeRegister,
            controlSignal = controlSignal
        )
    }

    private fun execute(idResult: DecodeResult): ExecutionResult {
        val controlSignal = idResult.controlSignal
        var src1 = mux(controlSignal.shift, idResult.readData2, idResult.readData1)
        src1 = mux(controlSignal.upperImm, idResult.immediate, src1)

        var src2 = mux(controlSignal.aluSrc, idResult.immediate, idResult.readData2)
        src2 = mux(controlSignal.shift, idResult.shiftAmt, src2)
        src2 = mux(controlSignal.upperImm, 16, src2)

        val aluResult = alu.operate(
            aluOp = controlSignal.aluOp,
            src1 = src1,
            src2 = src2
        )

        val aluValue = mux(controlSignal.jal, idResult.pc + 8, aluResult.value)

        val branchCondition = and(aluResult.isTrue, controlSignal.branch)
        var nextPc = mux(branchCondition, idResult.immediate, idResult.pc)
        nextPc = mux(controlSignal.jump, idResult.address, nextPc)
        nextPc = mux(controlSignal.jr, idResult.readData1, nextPc)

        return ExecutionResult(
            valid = true,
            pc = idResult.pc, // TODO :: only for logging
            aluValue = aluValue,
            memWriteValue = idResult.readData2,
            writeRegister = idResult.writeRegister,
            nextPc = nextPc,
            jump = (branchCondition || controlSignal.jump || controlSignal.jr),
            controlSignal = controlSignal
        )
    }

    private fun memoryAccess(exResult: ExecutionResult): MemoryAccessResult {
        val controlSignal = exResult.controlSignal
        val memReadValue = memory.read(
            memRead = controlSignal.memRead,
            address = exResult.aluValue,
        )

        memory.write(
            memWrite = controlSignal.memWrite,
            address = exResult.aluValue,
            value = exResult.memWriteValue
        )

        return MemoryAccessResult(
            valid = true,
            pc = exResult.pc, // TODO :: only for logging
            memReadValue = memReadValue,
            memWriteValue = exResult.memWriteValue,
            aluValue = exResult.aluValue,
            writeRegister = exResult.writeRegister,
            controlSignal = controlSignal
        )
    }

    private fun writeBack(maResult: MemoryAccessResult): WriteBackResult {
        if (!maResult.valid) {
            return WriteBackResult()
        }

        val controlSignal = maResult.controlSignal
        val regWriteValue = mux(controlSignal.memToReg, maResult.memReadValue, maResult.aluValue)

        if(controlSignal.regWrite) {
            registers.write(
                writeRegister = maResult.writeRegister,
                writeData = regWriteValue
            )
        }

        return WriteBackResult(
            valid = maResult.valid,
            pc = maResult.pc, // TODO :: only for logging
            writeRegister = maResult.writeRegister,
            regWriteValue = regWriteValue,
            controlSignal = controlSignal
        )
    }
}
interface ControlUnitInterface {
    fun process(): Int
}

open class Registers(
    size: Int
) {
    val registerSize = if (size < 32) 32 else size
    private val r: Array<Int> = Array(registerSize) { 0 }

    init {
        r[29] = 0x1000000
        r[31] = -1
    }

    operator fun get(register: Int) = r[register]

    fun write(writeRegister: Int, writeData: Int) {
        this.r[writeRegister] = writeData
    }
}

open class ScoreBoardingRegisters(
    size: Int
) {
    private val registers = Registers(size)
    private val valid: Array<Boolean> = Array(registers.registerSize) { true }
    private val tag: Array<Int> = Array(registers.registerSize) { 0 }

    operator fun get(register: Int) = registers[register]
    fun book(regWrite: Boolean, writeRegister: Int, tag: Int) {
        if (regWrite && writeRegister != 0) {
            this.valid[writeRegister] = false
            this.tag[writeRegister] = tag
        }
    }
    open fun write(regWrite: Boolean, writeRegister: Int, writeData: Int, tag: Int) {
        if (regWrite) {
            this.registers.write(writeRegister, writeData)
        }

        if (regWrite && this.tag[writeRegister] == tag) {
            this.valid[writeRegister] = true
        }
    }
    fun isValid(writeRegister: Int): Boolean {
        return this.valid[writeRegister]
    }
}
class ALUnit(
    private val operations: MutableMap<AluOp, (Int, Int) -> Int> = mutableMapOf()
) {

    init {
        operations[AluOp.ADDITION] = { src1, scr2 -> src1 + scr2 }
        operations[AluOp.SUBTRACTION] = { src1, scr2 -> src1 - scr2 }
        operations[AluOp.OR] = { src1, scr2 -> src1 or scr2 }
        operations[AluOp.SHIFT_LEFT] = { src1, scr2 -> src1 shl scr2 }
        operations[AluOp.SET_LESS_THAN] = { src1, scr2 -> if (src1 < scr2) 1 else 0 }
        operations[AluOp.NONE] = { _, _ -> 0 }
        operations[AluOp.EQUAL] = { src1, scr2 -> if (src1 == scr2) 1 else 0 }
        operations[AluOp.NOT_EQUAL] = { src1, scr2 -> if (src1 != scr2) 1 else 0 }
    }

    fun operate(aluOp: AluOp, src1: Int, src2: Int): AluResult {
        return AluResult(operations[aluOp]?.invoke(src1, src2)
            ?: throw IllegalArgumentException("Opcodes that cannot be computed : $aluOp"))
    }
}

data class AluResult(
    val value: Int,
    val isTrue: Boolean = value == 1
)

enum class AluOp {
    ADDITION,
    SUBTRACTION,
    OR,
    SHIFT_LEFT,
    SET_LESS_THAN,
    NONE,
    EQUAL,
    NOT_EQUAL;
}
data class ControlSignal(
    val opcode: Opcode = Opcode.SLL,
    val regDest: Boolean = opcode.type == Opcode.Type.R,
    val aluSrc: Boolean = (opcode.type != Opcode.Type.R)
            && (opcode != Opcode.BEQ)
            && (opcode != Opcode.BNE),
    val shift: Boolean = opcode == Opcode.SLL,
    val upperImm: Boolean = opcode == Opcode.LUI,
    val memToReg: Boolean = opcode == Opcode.LW,
    val regWrite: Boolean = (opcode != Opcode.SW) &&
            (opcode != Opcode.BEQ) &&
            (opcode != Opcode.BNE) &&
            (opcode != Opcode.J) &&
            (opcode != Opcode.JR),
    val memRead: Boolean = opcode == Opcode.LW,
    val memWrite: Boolean = opcode == Opcode.SW,
    val jump: Boolean = (opcode == Opcode.J) || (opcode == Opcode.JAL),
    val branch: Boolean = (opcode == Opcode.BNE || opcode == Opcode.BEQ),
    val jr: Boolean = (opcode == Opcode.JR),
    val jal: Boolean = (opcode == Opcode.JAL),
    val aluOp: AluOp = opcode.operation,
    var isEnd: Boolean = false
) {
    companion object {
        val NONE = ControlSignal(regWrite = false, memWrite = false, isEnd = false)
    }
}
class DataDependencyUnit(
    private val scoreBoardingRegisters: ScoreBoardingRegisters
) {
    fun hasHazard(readReg1: Int, readReg2: Int): Boolean{
        val valid1 = scoreBoardingRegisters.isValid(readReg1)
        val valid2 = scoreBoardingRegisters.isValid(readReg2)
        return !(valid1 && valid2)
    }
}
class DecodeUnit {

    fun parse(pc: Int, instruction: Int): ParsedInstruction {
        if(instruction == 0) {
            return ParsedInstruction.NOP
        }
        return ParsedInstruction(pc, instruction)
    }

    fun controlSignal(isValid: Boolean = true, opcode: Opcode): ControlSignal {
        if(!isValid) {
            return ControlSignal.NONE
        }
        return ControlSignal(opcode)
    }
}

data class ParsedInstruction(
    private val pc: Int,
    private val instruction: Int,
    val opcode: Opcode = Opcode.of(instruction),
    val rs: Int = instruction shr 21 and 0x1F,
    val rt: Int = instruction shr 16 and 0x1F,
    val rd: Int = instruction shr 11 and 0x1F,
    val shiftAmt: Int = instruction shr 6 and 0x1F,
    val immediate: Int = immediate(pc, instruction),
    val address: Int = address(pc, instruction)
) {
    companion object {

        val NOP = ParsedInstruction(0, 0, )

        fun immediate(pc: Int, instruction: Int): Int {
            val imm = instruction and 0xFFFF
            return when (Opcode.of(instruction)) {
                Opcode.ADDIU,
                Opcode.ADDI,
                Opcode.SLTI,
                Opcode.SW,
                Opcode.LW -> signExtension32(imm)
                Opcode.ORI -> zeroExtension32(imm)
                Opcode.BNE,
                Opcode.BEQ -> pc + branchAddress(imm)
                else -> imm
            }
        }

        fun address(pc: Int, instruction: Int): Int {
            val originAddress = instruction and 0x3FFFFFF
            return when (Opcode.of(instruction)) {
                Opcode.J,
                Opcode.JAL -> jumpAddress(pc, originAddress)
                else -> originAddress
            }
        }

        private fun signExtension32(num: Int) = num shl 16 shr 16

        private fun zeroExtension32(num: Int) = num shl 16 ushr 16

        private fun jumpAddress(pc: Int, address: Int): Int {
            val first4bit = (pc shr 28 and 0xF).toBinaryString(4)
            val last28bit = address.toBinaryString(26) + "00"
            return (first4bit + last28bit).toLong(2).toInt()
        }

        private fun branchAddress(immediate: Int): Int {
            val binaryImmediate = immediate.toBinaryString(16)
            return if (binaryImmediate.first() == '1') {
                ("11111111111111" + binaryImmediate + "00").toLong(2).toInt()
            } else {
                ("00000000000000" + binaryImmediate + "00").toLong(2).toInt()
            }
        }

        private fun Int.toBinaryString(digits: Int): String {
            val originNumber = Integer.toBinaryString(this)
            var newBinary = originNumber
            if (newBinary.length < digits) {
                for (i in 0 until digits - originNumber.length) {
                    newBinary = "0$newBinary"
                }
            }
            return newBinary
        }
    }
}
class EndFlag {

    var isEnd = false

    fun update(lastInstruction: Boolean) {
        if(!isEnd) {
            this.isEnd = lastInstruction
        }
    }
}
enum class Opcode(
    val code: Int,
    val type: Type,
    val operation: AluOp
) {
    ADDI(0x08, Type.I, AluOp.ADDITION),
    ADDIU(0x09, Type.I, AluOp.ADDITION),
    ADDU(0x21, Type.R, AluOp.ADDITION),
    BEQ(0x04, Type.I, AluOp.EQUAL),
    BNE(0x05, Type.I, AluOp.NOT_EQUAL),
    J(0x02, Type.J, AluOp.NONE),
    JAL(0x03, Type.J, AluOp.NONE),
    JR(0x08, Type.R, AluOp.NONE),
    LUI(0x0F, Type.I, AluOp.SHIFT_LEFT),
    LW(0x23, Type.I, AluOp.ADDITION),
    ORI(0x0D, Type.I, AluOp.OR),
    SLT(0x2A, Type.R, AluOp.SET_LESS_THAN),
    SLTI(0x0A, Type.I, AluOp.SET_LESS_THAN),
    SLL(0x00, Type.R, AluOp.SHIFT_LEFT),
    SW(0x2B, Type.I, AluOp.ADDITION),
    SUBU(0x23, Type.R, AluOp.SUBTRACTION);

    enum class Type { R, I, J }

    companion object {

        fun of(instruction: Int): Opcode {
            try {
                return of(instruction shr 26 and 0x3F, instruction and 0x3F)
            } catch (e: IllegalArgumentException) {
                throw IllegalArgumentException(
                    "Invalid opcode!! : instruction : 0x${instruction.toHexString(8)}\n"
                            + e.message
                )
            }
        }

        private fun of(op: Int, func: Int): Opcode {
            return values().find {
                if (op == 0)
                    it.type == Type.R && it.code == func
                else
                    it.type != Type.R && it.code == op
            } ?: throw IllegalArgumentException(
                "opcode : ${Integer.toBinaryString(op)}, function : ${Integer.toBinaryString(func)}"
            )
        }
    }
}
data class FetchResult(
    var valid: Boolean = false,
    val pc: Int = 0,
    val instruction: Int = 0
)

data class DecodeResult(
    var valid: Boolean = false,
    val pc: Int = 0,
    val dataHazard: Boolean = false,
    val shiftAmt: Int = 0,
    val immediate: Int = 0,
    val address: Int = 0,
    val readData1: Int = 0,
    val readData2: Int = 0,
    val writeRegister: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class ExecutionResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val aluValue: Int = 0,
    val memWriteValue: Int = 0,
    val writeRegister: Int = 0,
    val nextPc: Int = 0,
    val jump: Boolean = false,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class MemoryAccessResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val memReadValue: Int = 0,
    val memWriteValue: Int = 0,
    val aluValue: Int = 0,
    val writeRegister: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class WriteBackResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val writeRegister: Int = 0,
    val regWriteValue: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class CycleResult(
    val nextPc: Int = 0,
    val valid: Boolean = false,
    val value: Int = 0,
    val lastInstruction: Boolean = false,
    val lastCycle: Boolean = false
)

data class FetchResult(
    var valid: Boolean = false,
    val pc: Int = 0,
    val instruction: Int = 0
)

data class DecodeResult(
    var valid: Boolean = false,
    val pc: Int = 0,
    val dataHazard: Boolean = false,
    val shiftAmt: Int = 0,
    val immediate: Int = 0,
    val address: Int = 0,
    val readData1: Int = 0,
    val readData2: Int = 0,
    val writeRegister: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class ExecutionResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val aluValue: Int = 0,
    val memWriteValue: Int = 0,
    val writeRegister: Int = 0,
    val nextPc: Int = 0,
    val jump: Boolean = false,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class MemoryAccessResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val memReadValue: Int = 0,
    val memWriteValue: Int = 0,
    val aluValue: Int = 0,
    val writeRegister: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class WriteBackResult(
    val valid: Boolean = false,
    val pc: Int = 0, // TODO :: for logging
    val writeRegister: Int = 0,
    val regWriteValue: Int = 0,
    val controlSignal: ControlSignal = ControlSignal.NONE
)

data class CycleResult(
    val nextPc: Int = 0,
    val valid: Boolean = false,
    val value: Int = 0,
    val lastInstruction: Boolean = false,
    val lastCycle: Boolean = false
)

class StallUnit(
    var stallingCount: Int = 0
) {
    var freezePc: Int = 0
    var isMelt: Boolean = false
    var valid: Boolean = true

    fun next() {
        when (stallingCount) {
            0 -> isMelt = false
            1 -> {
                stallingCount = 0
                isMelt = true
                valid = true
            }
            else -> stallingCount--
        }
    }

    fun sleep(stallingCount: Int, pc : Int) {
        if (this.valid) {
            this.freezePc = pc
            this.valid = false
            this.stallingCount = stallingCount
        }
    }
}


open class Logger(
    private val loggingSignal: LoggingSignal
) {
    private var cycleCount = 0
    private var numberOfExecutedMA = 0
    private var numberOfWriteBack = 0
    private var numberOfTakenBranches = 0
    private val executedOpcodes = mutableMapOf<Opcode, Int>()
    private val executedOpcodeType = mutableMapOf<Opcode.Type, Int>()
    private val executedInstructionSet = mutableSetOf<Int>()

    companion object {
        val NONE = Logger(LoggingSignal())
    }

    open fun log(
        fetchResult: FetchResult,
        decodeResult: DecodeResult,
        executionResult: ExecutionResult,
        memoryAccessResult: MemoryAccessResult,
        writeBackResult: WriteBackResult
    ) {
        collect(fetchResult, decodeResult, executionResult, memoryAccessResult, writeBackResult)
        printCycleLog(fetchResult, decodeResult, executionResult, memoryAccessResult, writeBackResult)
    }

    open fun printCycleLog(
        fetchResult: FetchResult,
        decodeResult: DecodeResult,
        executionResult: ExecutionResult,
        memoryAccessResult: MemoryAccessResult,
        writeBackResult: WriteBackResult
    ) {
        printFetchResult(fetchResult)
        printDecodeResult(decodeResult)
        printExecutionResult(executionResult)
        printMemoryAccessResult(memoryAccessResult)
        printWriteBackResult(writeBackResult)
    }

    open fun collect(
        fetchResult: FetchResult,
        decodeResult: DecodeResult,
        executionResult: ExecutionResult,
        memoryAccessResult: MemoryAccessResult,
        writeBackResult: WriteBackResult
    ) {
        executedInstructionSet.add(fetchResult.instruction)

        if (decodeResult.valid) {
            executedOpcodes[decodeResult.controlSignal.opcode] =
                executedOpcodes.getOrDefault(decodeResult.controlSignal.opcode, 0) + 1
            executedOpcodeType[decodeResult.controlSignal.opcode.type] =
                executedOpcodeType.getOrDefault(decodeResult.controlSignal.opcode.type, 0) + 1
        }

        if (executionResult.valid) {
            if (executionResult.controlSignal.branch && executionResult.aluValue == 1) {
                numberOfTakenBranches++
            }
        }

        if (memoryAccessResult.valid) {
            if (memoryAccessResult.controlSignal.memRead || memoryAccessResult.controlSignal.memWrite) {
                numberOfExecutedMA++
            }
        }

        if (writeBackResult.valid) {
            if (writeBackResult.controlSignal.regWrite) {
                numberOfWriteBack++
            }
        }
    }

    fun printCycle(printOrNot: Boolean, cycleCount: Int) {
        if(!printOrNot) {
            return
        }
        checkPrintRange(cycleCount)
        this.cycleCount = cycleCount
        try {
            Thread.sleep(loggingSignal.sleepTime)
            if (!loggingSignal.cycle) return
            if (this.cycleCount % loggingSignal.cyclePrintPeriod == 0) {
                println("cycle : ${this.cycleCount}")
            }
        } catch (e: InterruptedException) {
        }
    }

    private fun checkPrintRange(cycleCount: Int) {
        if (cycleCount < loggingSignal.from && cycleCount < loggingSignal.to) {
            loggingSignal.cycle = true
            loggingSignal.fetch = true
            loggingSignal.decode = true
            loggingSignal.execute = true
            loggingSignal.memoryAccess = true
            loggingSignal.writeBack = true
        } else {
            loggingSignal.cycle = false
            loggingSignal.fetch = false
            loggingSignal.decode = false
            loggingSignal.execute = false
            loggingSignal.memoryAccess = false
            loggingSignal.writeBack = false
        }
    }

    fun printCycle(cycleCount: Int) {
        printCycle(true, cycleCount)
    }

    private fun printFetchResult(result: FetchResult) {
        if (!loggingSignal.fetch) return
        if (!result.valid) {
            printStep("IF", result.pc)
            printNop()
            return
        }

        printStep("IF", result.pc)
        print("pc : 0x${(result.pc).toHexString(2)}, ")
        print("instruction : 0x${result.instruction.toHexString(8)}")
        println()
    }

    private fun printDecodeResult(result: DecodeResult) {
        val opcode = result.controlSignal.opcode
        if (!loggingSignal.decode) return
        if (!result.valid) {
            printStep("ID", result.pc)
            printNop()
            return
        }

        printStep("ID", result.pc)

        var msg = "opcode : ${opcode}, "
        if (opcode.type == Opcode.Type.R) {
            msg += "readData1 : ${result.readData1}, readData2 : ${result.readData2}"
        }

        if (opcode.type == Opcode.Type.I) {
            msg += "readData1 : ${result.readData1} [0x${result.readData1.toHexString()}], " +
                    "immediate : ${result.immediate} [0x${result.immediate.toHexString()}]"
        }

        if (opcode.type == Opcode.Type.J) {
            msg += "address : 0x${result.address.toHexString()}"
        }
        println(msg)
    }

    private fun printExecutionResult(result: ExecutionResult) {
        if (!loggingSignal.execute) return
        if (!result.valid) {
            printStep("EX", result.pc)
            printNop()
            return
        }

        printStep("EX", result.pc)
        val msg = "result : ${result.aluValue} [0x${result.aluValue.toHexString()}], " +
                "nextPc : 0x${result.nextPc.toHexString()}"
        println(msg)
    }

    private fun printMemoryAccessResult(result: MemoryAccessResult) {
        if (!loggingSignal.memoryAccess) return
        if (!result.valid) {
            printStep("MA", result.pc)
            printNop()
            return
        }
        printStep("MA", result.pc)
        var msg = ""
        if (result.controlSignal.memRead) {
            msg = "M[0x${result.aluValue.toHexString()}] = ${result.memReadValue} [0x${result.memReadValue.toHexString()}]"
        }
        if (result.controlSignal.memWrite) {
            msg = "M[0x${result.aluValue.toHexString()}] = ${result.memWriteValue} [0x${result.memWriteValue.toHexString()}]"
        }
        println(msg)
    }

    private fun printWriteBackResult(result: WriteBackResult) {
        if (!loggingSignal.writeBack) return
        if (!result.valid) {
            printStep("WB", result.pc)
            printNop()
            println()
            return
        }

        printStep("WB", result.pc)
        var msg = ""
        if (result.controlSignal.regWrite) {
            msg = "R[${result.writeRegister}] = ${result.regWriteValue} [0x${result.regWriteValue.toHexString()}]"
        }
        println(msg + "\n")
    }

    fun printProcessResult(resultValue: Int) {
        if (!loggingSignal.resultInformation) return

        println("=== Result === ")
        println("cycle count : $cycleCount")
        println("result value : $resultValue")
        println()

        println("=== executed instructions ===")
        println("executed memory access : $numberOfExecutedMA")
        println("executed taken branches : $numberOfTakenBranches")
        println("executed write back : $numberOfWriteBack")
        println("kinds : ${executedInstructionSet.size}")
        print("[] : ")
        executedInstructionSet.forEach { print("0x${it.toHexString(8)} ") }
        println()
        println()

        println("=== executed opcode type ===")
        println("type R : ${executedOpcodeType.getOrDefault(Opcode.Type.R, 0)}")
        println("type I : ${executedOpcodeType.getOrDefault(Opcode.Type.I, 0)}")
        println("type J : ${executedOpcodeType.getOrDefault(Opcode.Type.J, 0)}")
        println()

        println("=== executed opcode === ")
        println("kinds : ${executedOpcodes.size}")
        print("[] : ")
        executedOpcodes.forEach { print("$it ") }
        println()
    }

    private fun printStep(stepName: String, pc: Int) {
        print("[$stepName] [$pc] :: ")
    }

    private fun printNop() {
        println("[NOP]")
    }
}
data class LoggingSignal(
    var cycle: Boolean = false,
    var cyclePrintPeriod: Int = 1,
    var fetch: Boolean = false,
    var decode: Boolean = false,
    var execute: Boolean = false,
    var memoryAccess: Boolean = false,
    var writeBack: Boolean = false,
    var resultInformation: Boolean = false,
    var sleepTime: Long = 0L,
    var from: Int = 0,
    var to: Int = Int.MAX_VALUE
)
fun Int.toHexString(): String {
    return Integer.toHexString(this).uppercase()
}

fun Int.toHexString(digits: Int): String {
    val hexString = Integer.toHexString(this)
    var newBinary = hexString
    if (newBinary.length < digits) {
        for (i in 0 until digits - hexString.length) {
            newBinary = "0$newBinary"
        }
    }
    return newBinary.uppercase()
}

class PipeLineLogger(loggingSignal: LoggingSignal) : Logger(loggingSignal) {
    private val cycleLogs = Array(5) { CycleLog() }

    override fun log(
        fetchResult: FetchResult,
        decodeResult: DecodeResult,
        executionResult: ExecutionResult,
        memoryAccessResult: MemoryAccessResult,
        writeBackResult: WriteBackResult
    ) {
        cycleLogs[0].fetchResult = fetchResult
        cycleLogs[1].decodeResult = decodeResult
        cycleLogs[2].executionResult = executionResult
        cycleLogs[3].memoryAccessResult = memoryAccessResult
        cycleLogs[4].writeBackResult = writeBackResult

        collect(fetchResult, decodeResult, executionResult, memoryAccessResult, writeBackResult)
        printCycleLog(
            fetchResult = cycleLogs[4].fetchResult,
            decodeResult = cycleLogs[4].decodeResult,
            executionResult = cycleLogs[4].executionResult,
            memoryAccessResult = cycleLogs[4].memoryAccessResult,
            writeBackResult = cycleLogs[4].writeBackResult
        )
        flushCycleLog()
    }

    override fun printCycleLog(
        fetchResult: FetchResult,
        decodeResult: DecodeResult,
        executionResult: ExecutionResult,
        memoryAccessResult: MemoryAccessResult,
        writeBackResult: WriteBackResult
    ) {
        if (
            fetchResult.pc == decodeResult.pc &&
            decodeResult.pc == executionResult.pc &&
            executionResult.pc == memoryAccessResult.pc &&
            memoryAccessResult.pc == writeBackResult.pc &&
            fetchResult.valid &&
            decodeResult.valid &&
            executionResult.valid &&
            memoryAccessResult.valid &&
            writeBackResult.valid
        ) {
            super.printCycleLog(fetchResult, decodeResult, executionResult, memoryAccessResult, writeBackResult)
        }
    }

    private fun flushCycleLog() {
        cycleLogs[4] = cycleLogs[3]
        cycleLogs[3] = cycleLogs[2]
        cycleLogs[2] = cycleLogs[1]
        cycleLogs[1] = cycleLogs[0]
        cycleLogs[0] = CycleLog()
    }
}

data class CycleLog(
    var fetchResult: FetchResult = FetchResult(),
    var decodeResult: DecodeResult = DecodeResult(),
    var executionResult: ExecutionResult = ExecutionResult(),
    var memoryAccessResult: MemoryAccessResult = MemoryAccessResult(),
    var writeBackResult: WriteBackResult = WriteBackResult(),
)

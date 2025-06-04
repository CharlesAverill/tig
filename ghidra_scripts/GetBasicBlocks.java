// Modified from ofrak (https://ofrak.com/)
import com.google.common.base.Strings;
import ghidra.app.util.headless.HeadlessScript;
import ghidra.app.script.GhidraState;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressRange;
import ghidra.program.model.address.AddressRangeIterator;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.block.BasicBlockModel;
import ghidra.program.model.block.CodeBlock;
import ghidra.program.model.block.CodeBlockIterator;
import ghidra.program.model.block.CodeBlockModel;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.mem.MemoryBlockSourceInfo;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemBuffer;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;
import ghidra.program.model.lang.Register;
import ghidra.program.model.lang.RegisterValue;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.block.CodeBlockReferenceIterator;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.RefType;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.math.BigInteger;

public class GetBasicBlocks extends HeadlessScript {
    @Override
    public void run() throws Exception {
        try {
            Function func = getFirstFunction();
            List<String> all_responses = new ArrayList<>();

            if (func == null) {
                System.out.println("No Function Found >o<");
            } else {
                while (func != null) {
                    //System.out.println("===  " + func.getName());
                    Address startAddr = func.getEntryPoint();
                    String response;

                    response = new GetBasicBlocks.Result(startAddr).toJson();
                    //for (String s: response.split(", "))
                    //    System.out.println(s);
                    all_responses.add(
                            "{" +
                            String.format("\"function_name\":\"%s\",", func.getName()) +
                            "\"blocks\":" + response +
                            "}"
                            );

                    func = getFunctionAfter(func);
                }
            }
            try (PrintWriter out = new PrintWriter("GetBasicBlocks_result.json")) {
                out.println(all_responses);
            } catch(Exception e) {
                println(e.toString());
                throw e;
            }


        } catch(Exception e) {
            println(e.toString());
            throw e;
        }
    }

    class Result {
        final List<GetBasicBlocks.ResultBasicBlock> basicBlocks;

        Result(Address startAddr) throws CancelledException {
            CodeBlockModel blockModel = new BasicBlockModel(currentProgram);
            Function function = currentProgram.getFunctionManager().getFunctionAt(startAddr);

            this.basicBlocks = new ArrayList<>();
            CodeBlockIterator iterator = blockModel.getCodeBlocksContaining(function.getBody(), monitor);
            while (iterator.hasNext()) {
                this.basicBlocks.add(new GetBasicBlocks.ResultBasicBlock(function.getEntryPoint(), iterator.next()));
            }
        }

        String toJson() {
            String bbString = basicBlocks.stream()
                    .map(GetBasicBlocks.ResultBasicBlock::toJson)
                    .collect(Collectors.joining(", "));
            return String.format("[%s]", bbString);
        }
    }


    class ResultBasicBlock {
        final long bb_start_vaddr;
        final long bb_size;
        final boolean is_exit_point;
        final boolean is_entry_point;
        final List<String> exit_vaddrs;
        final List<String> source_vaddrs;
        final List<GetBasicBlocks.ResultInstruction> instructions;
        final List<String> instr_jsons;

        String instruction_mode;

        ResultBasicBlock(Address functionStart, CodeBlock codeBlock) throws CancelledException {
            if (codeBlock.getNumAddressRanges() > 1) {
                throw new RuntimeException("This is unexpected... figure out why this happens");
            }

            AddressRange addressRange = codeBlock.getAddressRanges().next();
            Address bb_startAddr = addressRange.getMinAddress();
            Address bb_endAddr = addressRange.getMaxAddress();

            this.bb_start_vaddr = bb_startAddr.getOffset();
            this.bb_size = addressRange.getLength();

            Function function = currentProgram.getFunctionManager().getFunctionAt(functionStart);

            //- Determine is_exit_point or get exit_vaddr
            this.exit_vaddrs = new ArrayList<>();

            boolean is_exit_point = true;
            long exit_vaddr = -1;
            CodeBlockReferenceIterator iterator = codeBlock.getDestinations(monitor);
            while (iterator.hasNext()) {
                CodeBlock successor_bb = iterator.next().getDestinationBlock();
                AddressRange successor_bb_addressRange = successor_bb.getAddressRanges().next();
                // Check if the successor is in the function (in the ComplexBlock), discard the destinations that are not.
                if (successor_bb_addressRange.getMinAddress().getOffset() >= function.getBody().getMinAddress().getOffset() 
                        && successor_bb_addressRange.getMaxAddress().getOffset() <= function.getBody().getMaxAddress().getOffset()
                        )
                {
                    is_exit_point = false;
                    if(successor_bb_addressRange.getMinAddress().getOffset() > addressRange.getMaxAddress().getOffset()) {
                        exit_vaddr = successor_bb_addressRange.getMinAddress().getOffset();
                        this.exit_vaddrs.add(Long.toUnsignedString(exit_vaddr));
                    }
                }
            }
            this.is_exit_point = is_exit_point;

            //- Get source_vaddrs
            if (this.bb_start_vaddr == functionStart.getOffset())
                this.is_entry_point = true;
            else
                this.is_entry_point = false;

            this.source_vaddrs = new ArrayList<>();
            iterator = codeBlock.getSources(monitor);
            while (iterator.hasNext()) {
                CodeBlock source_bb = iterator.next().getSourceBlock();
                AddressRange source_bb_addressRange = source_bb.getAddressRanges().next();
                long source_vaddr = source_bb_addressRange.getMinAddress().getOffset();
                this.source_vaddrs.add(Long.toUnsignedString(source_vaddr));
            }

            //- Try to get the Thumb register and check its value
            try {
                Register tmode_register = currentProgram.getRegister("TMode");
                RegisterValue function_mode = currentProgram.getProgramContext().getRegisterValue(tmode_register, addressRange.getMinAddress());
                this.instruction_mode = function_mode.getUnsignedValueIgnoreMask().equals(BigInteger.ONE) ? "THUMB" : "NONE" ;
            } catch(Exception e) {
                this.instruction_mode = "NONE";
            }

            //- Try to get the vle register and check its value
            try {
                Register vle_register = currentProgram.getRegister("vle");
                RegisterValue function_mode = currentProgram.getProgramContext().getRegisterValue(vle_register, addressRange.getMinAddress());
                this.instruction_mode = function_mode.getUnsignedValueIgnoreMask().equals(BigInteger.ONE) ? "VLE" : this.instruction_mode;
            } catch(Exception e) {
                // Pass
            }

            //- Get Instructions
            this.instructions = new ArrayList<>();
            this.instr_jsons = new ArrayList<>();
            
            Instruction instruction = getInstructionAt(bb_startAddr);
            if (instruction == null) {
                instruction = getInstructionAfter(bb_startAddr);
            }
            while (instruction != null && instruction.getAddress().getOffset() < bb_endAddr.getOffset()) {
                this.instructions.add(new GetBasicBlocks.ResultInstruction(instruction));
                instruction = getInstructionAfter(instruction);

            }
            for (GetBasicBlocks.ResultInstruction instr: this.instructions) 
                this.instr_jsons.add(instr.toJson());

        }

        String toJson() {
            return "{" +
                String.format(
                        "\"bb_start_vaddr\":%s,",
                        Long.toUnsignedString(bb_start_vaddr)
                        ) + 
                String.format(
                        "\"bb_size\":%s,",
                        Long.toUnsignedString(bb_size)
                        ) + 
                String.format(
                        "\"is_exit_point\":%b,",
                        is_exit_point
                        ) + 
                String.format(
                        "\"exit_vaddrs\":[%s],", 
                        String.join(",", exit_vaddrs)
                        ) + 
                String.format(
                        "\"is_entry_point\":%b,",
                        is_entry_point
                        ) + 
                String.format(
                        "\"source_vaddrs\":[%s],", 
                        String.join(",", source_vaddrs)
                        ) + 
                String.format(
                        "\"instr_mode\":\"%s\",",
                        instruction_mode
                        ) + 
                String.format(
                        "\"instructions\":[%s]",
                        String.join(", ", this.instr_jsons)
                        ) + 
                "}";
        }
    }

    class ResultInstruction {
        final long instr_offset;
        final long instr_size;
        final String mnem;
        final String operands;
        final String registers_written;
        final String registers_read;
        final String results;
        final Object[] results_objects;
        final String instruction_str;
        final String instruction_byte;
        final boolean is_big_endian;

        ResultInstruction(Instruction instruction) {
            StringBuilder ops = new StringBuilder();
            StringBuilder regs_read = new StringBuilder();
            StringBuilder regs_written = new StringBuilder();
            StringBuilder res = new StringBuilder();

            this.instruction_str = instruction.toString();

            this.results_objects = instruction.getResultObjects();
            this.instr_offset = instruction.getAddress().getOffset();
            this.instr_size = instruction.getLength();
            this.mnem = instruction.getMnemonicString();

            for (int i = 0; i < instruction.getNumOperands(); i++) {
                ops.append(instruction.getDefaultOperandRepresentation​(i));
                if (i != instruction.getNumOperands() - 1) {
                    ops.append(",");
                }
                if (instruction.getOperandRefType(i) == RefType.READ) {
                    regs_read.append(instruction.getOpObjects(i)[instruction.getOpObjects(i).length-1].toString());
                    if (i != instruction.getNumOperands() - 1) {
                        regs_read.append(",");
                    }
                }
                if (instruction.getOperandRefType(i) == RefType.WRITE) {
                    regs_written.append(instruction.getOpObjects(i)[instruction.getOpObjects(i).length-1].toString());
                     if (i != instruction.getNumOperands() - 1) {
                        regs_written.append(",");
                    }
                }
                if (instruction.getOperandRefType(i) == RefType.READ_WRITE) {
                    regs_read.append(instruction.getOpObjects(i)[instruction.getOpObjects(i).length-1].toString());
                    regs_written.append(instruction.getOpObjects(i)[instruction.getOpObjects(i).length-1].toString());
                    if (i != instruction.getNumOperands() - 1) {
                        regs_read.append(",");
                        regs_written.append(",");
                    }
                }
            }
            for (int i = 0; i < results_objects.length; i++) {
                res.append(results_objects[i]);
                if (i != results_objects.length - 1) {
                    res.append(",");
                }
            }

            this.operands = ops.toString();
            this.registers_read = regs_read.toString();
            this.registers_written = regs_written.toString();
            this.results = res.toString();

            String binary = "";
            MemBuffer membuf = instruction.getInstructionContext().getMemBuffer();
            try {
                byte b = membuf.getByte(0);
                for (int i = 0; i < instruction.getLength(); i++) {
                    binary += String.format("%02X", membuf.getByte(i));
                }
            } catch(MemoryAccessException e) {
                println("MemoryAccessException" + e.toString());
            }
            this.instruction_byte = binary;
            this.is_big_endian = membuf.isBigEndian();
        }

        String toJson() {
            return 
                "{" + 
                String.format(
                        "\"instr_offset\":%s,",
                        Long.toUnsignedString(instr_offset) 
                        ) +
                String.format(
                        "\"instr_size\":%s,",
                        Long.toUnsignedString(instr_size) 
                        ) +
                String.format(
                        "\"mnem\":\"%s\",",
                        mnem 
                        ) +
                String.format(
                        "\"operands\":\"%s\",",
                        operands 
                        ) +
                String.format(
                        "\"regs_read\":\"%s\",",
                        registers_read 
                        ) +
                String.format(
                        "\"regs_written\":\"%s\",",
                        registers_written
                        ) +
                String.format(
                        "\"results\":\"%s\",",
                        results
                        ) +
                String.format(
                        "\"instruction_str\":\"%s\",",
                        instruction_str
                        ) +
                String.format(
                        "\"instruction_byte\":\"%s\",",
                        instruction_byte
                        ) +
                String.format(
                        "\"is_big_endian\":\"%b\"",
                        is_big_endian
                        ) +
                "}";
        }
    }

}

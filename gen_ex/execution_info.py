import sys
sys.path.append("/usr/lib/python3.8/site-packages")
from typing import Dict, List, Tuple, Union
from triton import MemoryAccess, TritonContext
from enum import Enum
import copy
import hashlib
import logging

# TODO: Add more
# String identifiers for which registers are used for input arguments
ARGUMENT_REGISTERS = ["rdi", "edi", "rsi", "esi", "rdx", "edx", "rcx", "ecx", "r8", "r9"]
# String identifiers for which registers are used for output arguments
OUTPUT_REGISTERS = {"rax", "eax"}

class InstructionType(Enum):
    NORMAL_INST = 0
    CALL_INST = 1
    LEAVE_INST = 2
    RET_INST = 3

class InstructionInfo():
    # Which specific instruction is being executed
    eip : int
    # Whether this is the first instruction after a call
    first_instr : bool
    # the address of the instruction
    i_addr : int
    # the ith instruction in the program
    i_count : int
    # An enum identifier for the type of instruction used to determine
    # whether we are leaving/entering a function
    inst_type : InstructionType
    # The bytes of an instruction, used to determine the uniqueness of a function
    opcode : bytes
    # The registers read along with their values
    r_regs : Dict[str, int] # reg name -> val
    # The registers written along with their values
    w_regs : Dict[str, int] # reg name -> val
    # Addresses read and the value read
    r_addrs : Dict[int, Tuple[int, int]] # address -> (size, val)
    # Addresses written and the values written
    w_addrs : Dict[int, Tuple[int, int]] # address -> (size, val)
    # The symbolic semantics of instruction
    # None should be Register but I cannot find where it is imported from
    smt : List[Tuple[Union[None, MemoryAccess], str]]

    # return values
    return_regs : Dict[str, int]

    def __init__(self, eip : int, first_instr : bool, i_addr : int, i_count : int, inst_type : InstructionType, r_regs : Dict[str, int], w_regs : Dict[str, int], \
                r_addrs : Dict[int, Tuple[int, int]], w_addrs : Dict[int, Tuple[int, int]], smt : List[str], opcode : bytes):
        self.eip = eip
        self.first_instr = first_instr
        self.i_addr = i_addr
        self.i_count = i_count
        self.inst_type = inst_type
        self.r_regs = r_regs
        self.w_regs = w_regs
        self.r_addrs = r_addrs
        self.w_addrs = w_addrs
        self.smt = smt
        self.opcode = opcode
        
        self.return_regs = {}
        for _or in OUTPUT_REGISTERS:
            self.return_regs.update({_or : None})

class FunctionInfo():
    ii : List[InstructionInfo]
    call_depth : int
    # input arguments
    i_args : Dict[Tuple[int, int], Tuple[int, int]] # (address ebp, negative offset) -> (size, value)
    o_args : Dict[str, int] # reg -> value
    # TODO: unused as of now
    initial_memory : List[Tuple[int, int]]
    final_memory : List[Tuple[int, int]]
    # TODO: unused as of now
    inital_registers : List[Tuple[str, int]]
    final_registers : List[Tuple[str, int]]

    identifier : int # first instruction in the function

    def __init__(self, ii : List[InstructionInfo], call_depth : int):
        self.ii = ii
        self.call_depth = call_depth
        self.i_args = {}
        self.o_args = {}
        # first_instr must be true if call_depth > 0
        if call_depth > 0:
            assert(ii[0].first_instr == True)
        self.identifier = ii[0].i_addr

    def determine_input_arguments(self):
        """
            Input arguments can be accessed by copying RDI, RSI and so on onto the stack
            Caller:
                mov edi, eax
                call 0x113c
            Callee:
                ...
                mov dword ptr [rbp - 4], edi
        """
        for i in self.ii:
            # 1. if we are reading rbp
            # 2. we are pulling from an ARGUMENT_REGISTERS
            # 3. we are writing to 4 or 8 offset from rbp value
            if "rbp" in i.r_regs \
                    and len(set(i.r_regs.keys()).intersection(ARGUMENT_REGISTERS)) > 0:
                assert(len(set(i.r_regs.keys()).intersection(ARGUMENT_REGISTERS)) == 1)
                if i.r_regs["rbp"] - 4 in i.w_addrs.keys():
                    assert(i.r_regs["rbp"] - 4 in i.w_addrs.keys())
                    self.i_args.update({(i.r_regs["rbp"], -4) : i.w_addrs[i.r_regs["rbp"] - 4]})
                elif i.r_regs["rbp"] - 8 in i.w_addrs.keys():
                    assert(i.r_regs["rbp"] - 8 in i.w_addrs.keys())
                    self.i_args.update({(i.r_regs["rbp"], -8) : i.w_addrs[i.r_regs["rbp"] - 8]})
                else:
                    logging.debug("[FunctionInfo] determine_number_input_arguments: Different offset from RBP detected. RBP " + str(i.r_regs["rbp"]) + ", written addresses " + str(i.w_addrs))
            elif "ebp" in i.r_regs:
                logging.debug("[FunctionInfo] determine_number_input_arguments: EBP detected even though we are using 64bit")
                exit(-1)

    def determine_output_arguments(self):
        """
            0x115e: add eax, edx
                Read Registers:eax,0xf|edx,0xe|
                Written Registers:eax,0xf
            0x1160: leave
            0x1161: ret

            We process bottom up
        """
        regs_not_yet_used = copy.deepcopy(OUTPUT_REGISTERS)
        ret_seen = False
        ret_instruction = None
        leave_seen = False
        for i in range(len(self.ii) - 1, -1, -1):
            ii = self.ii[i]
            # see ret
            if ii.inst_type == InstructionType.RET_INST and ret_seen == False and leave_seen == False:
                ret_seen = True
                ret_instruction = ii
            # see ret first then leave
            # elif ii.inst_type == InstructionType.LEAVE_INST and ret_seen == True and leave_seen == False:
            #     leave_seen = True
            # TODO: Do we need to care about seeing leave?
            # seen ret start trying to find output registers
            if ii.inst_type == InstructionType.NORMAL_INST and len(set(ii.w_regs.keys()).intersection(regs_not_yet_used)) > 0 \
                    and ret_seen == True: 
                    # leave_seen == True \
                o_reg = set(ii.w_regs.keys()).intersection(regs_not_yet_used)
                assert(len(o_reg) == 1)
                for _or in o_reg:
                    self.o_args.update({_or : ret_instruction.return_regs[_or]})
                    regs_not_yet_used.remove(_or)
            
    
class ExecutionInfo():
    ii : List[InstructionInfo]
    # functions are stored in the reverse order they are called
    # index 0 will be the function that is called last
    # index len(fi) - 1 will be main

    # key: int call depth
    # value: List[FunctionInfo] at that call depth
    fi : Dict[int, List[FunctionInfo]]

    # func_0 represents the top level call to the main function
    func_0_init_regs : Dict[str, int]
    func_0_init_memory : Dict[str, int]

    def __init__(self):
        self.ii = []
        self.fi = {}
        self.func_0_init_regs = {}

    def set_init_regs(self, ctx : TritonContext):    
        for reg in ctx.getAllRegisters():
            self.func_0_init_regs.update({reg.getName() : ctx.getConcreteRegisterValue(reg)})

    def split_function(self):
        """
            this operates on the assumption that the function is either beginning withe first instruction
            in ii or the first instruction after a call.  a function terminates when we hit a ret
        """
        
        call_count = 0
        call_depth = 0
        call_idx = []
        ret_count = 0
        ret_idx = []
        parsed = []

        f_start = {}
        f_end = {}
        # first instruction always belongs to the first function
        call_idx.append((0, call_depth))
        f_start.update({0 : [(0,0)]})
        for i in range(len(self.ii)):
            if self.ii[i].inst_type == InstructionType.CALL_INST:
                call_count += 1
                call_depth += 1
                # next instruction after a call is a new function
                call_idx.append((i + 1, call_depth))
                if call_depth not in f_start.keys():
                    f_start.update({call_depth : []})
                f_start[call_depth].append((i + 1, call_depth))
            elif self.ii[i].inst_type == InstructionType.RET_INST:
                ret_count += 1
                ret_idx.append((i, call_depth))
                if call_depth not in f_end.keys():
                    f_end.update({call_depth : []})
                f_end[call_depth].append((i, call_depth))
                call_depth += -1
            parsed.append(False)
        # reverse ret_idx to match call_idx
        ret_idx.reverse()
        # assert(call_count == ret_count)
        assert(len(call_idx) == len(ret_idx))

        # for reverse ordering of call depth
        for cd in sorted(f_start.keys(), reverse=True):
            # for each function at that call depth
            for idx in range(len(f_start[cd])):
                s = f_start[cd][idx]
                e = f_end[cd][idx]
                assert(s[1] == e[1]) # start and end must be same call depth
                f_insns = []
                for ii_idx in range(s[0], e[0] + 1, 1):
                    if parsed[ii_idx] == False:
                        f_insns.append(self.ii[ii_idx])
                        parsed[ii_idx] = True
                f_info = FunctionInfo(f_insns, s[1]) # s[1] is call depth
                if s[1] not in self.fi.keys():
                    self.fi.update({s[1] : []})
                self.fi[s[1]].append(f_info)
        
        # for k in self.fi.keys():
        #     logging.debug("###", k, "###")
        #     for v in self.fi[k]:
        #         for ii in v.ii:
        #             logging.debug(ii.i_count, end=" : ")
        #         logging.debug()
        #     logging.debug("######")

    def extract_function_input_output(self):
        """
            https://en.wikipedia.org/wiki/X86_calling_conventions
            We are assuming x86-64 and System-V calling convention

            ### INPUT ARGS ###
            The first six integer or pointer arguments are passed in registers
            RDI, RSI, RDX, RCX, R8, R9 (R10 is used as a static chain pointer in case of nested functions),
            while XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6 and XMM7 are used for the first floating point arguments.

            As in the Microsoft x64 calling convention, additional arguments are passed on the stack.

            If the callee wishes to use registers RBX, RSP, RBP, and R12???R15, 
            it must restore their original values before returning control to the caller. 
            All other registers must be saved by the caller if it wishes to preserve their values.

            TODO: Currently only accounting for RDI, RSI, RDX, RCX, R8, R9

            ### OUTPUT ARGS ###
            Integer return values up to 64 bits in size are stored in RAX while values up to 128 bit 
            are stored in RAX and RDX. Floating-point return values are similarly stored in XMM0 and XMM1.
            The wider YMM and ZMM registers are used for passing and returning wider values in place of XMM 
            when they exist.

            TODO: Currently only handling RAX
        """
        for cd in self.fi.keys():
            for fi in self.fi[cd]:
                logging.debug(hex(fi.identifier))
                fi.determine_input_arguments()
                logging.debug(fi.i_args)
                fi.determine_output_arguments()
                logging.debug(fi.o_args)


    def create_init_smt(self):
        """
            TODO: Create variables in SMT for the memory region used
                and all registers used
        """
        a = 0

    def create_final_assigment_smt(self):
        """
            TODO: Create the final SMT that states the final values
                of all the memory and 
        """

    def compose_smt(self):
        """
            TODO: Compose all SMT together
        """
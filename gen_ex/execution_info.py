from typing import Dict, List, Tuple, Union
from triton import MemoryAccess, TritonContext
from enum import Enum

# String identifiers for which registers are used for input arguments
ARGUMENT_REGISTERS = {"rdi", "edi", "rsi", "esi", "rdx", "edx", "rcx", "ecx", "r8", "r9"}

class InstructionType(Enum):
    NORMAL_INST = 0
    CALL_INST = 1
    RET_INST = 2

class InstructionInfo():
    # Which specific instruction is being executed
    eip : int
    # 0 = normal instruction
    # 1 = call
    # 2 = ret
    inst_type : InstructionType
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

    def __init__(self, eip : int, inst_type : InstructionType, r_regs : Dict[str, int], w_regs : Dict[str, int], \
                r_addrs : Dict[int, Tuple[int, int]], w_addrs : Dict[int, Tuple[int, int]], smt : List[str]):
        self.eip = eip
        self.inst_type = inst_type
        self.r_regs = r_regs
        self.w_regs = w_regs
        self.r_addrs = r_addrs
        self.w_addrs = w_addrs
        self.smt = smt

class FunctionInfo():
    ii : List[InstructionInfo]
    call_depth : int
    # input arguments
    i_args : Dict[int, int] # address ebp -> value
    # TODO: unused as of now
    initial_memory : List[Tuple[int, int]]
    final_memory : List[Tuple[int, int]]
    # TODO: unused as of now
    inital_registers : List[Tuple[str, int]]
    final_registers : List[Tuple[str, int]]

    def __init__(self, ii : List[InstructionInfo], call_depth : int):
        self.ii = ii
        self.call_depth = call_depth
        self.i_args = {}

    def determine_number_input_arguments(self):
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
                    self.i_args.update({i.r_regs["rbp"] - 4 : i.w_addrs[i.r_regs["rbp"] - 4]})
                elif i.r_regs["rbp"] - 8 in i.w_addrs.keys():
                    assert(i.r_regs["rbp"] - 8 in i.w_addrs.keys())
                    self.i_args.update({i.r_regs["rbp"] - 8 : i.w_addrs[i.r_regs["rbp"] - 8]})
                else:
                    print("[FunctionInfo] determine_number_input_arguments: Different offset from RBP detected. RBP", i.r_regs["rbp"], ", written addresses", i.w_addrs)
            elif "ebp" in i.r_regs:
                print("[FunctionInfo] determine_number_input_arguments: EBP detected even though we are using 64bit")
                exit(-1)
    
class ExecutionInfo():
    ii : List[InstructionInfo]
    # functions are stored in the reverse order they are called
    # index 0 will be the function that is called last
    # index len(fi) - 1 will be main
    fi : List[FunctionInfo]

    # func_0 represents the top level call to the main function
    func_0_init_regs : Dict[str, int]
    func_0_init_memory : Dict[str, int]

    def __init__(self):
        self.ii = []
        self.fi = []
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
        # first instruction always belongs to the first function
        call_idx.append((0, call_depth))
        for i in range(len(self.ii)):
            if self.ii[i].inst_type == InstructionType.CALL_INST:
                call_count += 1
                call_depth += 1
                call_idx.append((i, call_depth))
            elif self.ii[i].inst_type == InstructionType.RET_INST:
                ret_count += 1
                ret_idx.append((i, call_depth))
                call_depth += -1
            parsed.append(False)
        # reverse ret_idx to match call_idx
        ret_idx.reverse()
        # assert(call_count == ret_count)
        assert(len(call_idx) == len(ret_idx))

        for f_count in range(len(call_idx) - 1, -1, -1):
            f_insns = []
            f_call_depth = call_idx[f_count][1]
            for i in range(call_idx[f_count][0], ret_idx[f_count][0] + 1):
                if parsed[i] == False:
                    f_insns.append(self.ii[i])
                    parsed[i] = True
            f_info = FunctionInfo(f_insns, f_call_depth)
            self.fi.append(f_info)

        for fi in self.fi:
            print(len(fi.ii))
    
    def extract_function_input_arguments(self):
        """
            https://en.wikipedia.org/wiki/X86_calling_conventions
            We are assuming x86-64 and System-V calling convention

            The first six integer or pointer arguments are passed in registers
            RDI, RSI, RDX, RCX, R8, R9 (R10 is used as a static chain pointer in case of nested functions),
            while XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6 and XMM7 are used for the first floating point arguments.
        """
        for fi in self.fi:
            fi.determine_number_input_arguments()
            print(fi.i_args)


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
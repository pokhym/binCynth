from typing import Dict, List, Tuple, Union
from triton import MemoryAccess, TritonContext
from enum import Enum

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
    r_regs : List[Tuple[str, int]]
    # The registers written along with their values
    w_regs : List[Tuple[str, int]]
    # Addresses read and the value read
    r_addr : List[Tuple[int, int]]
    # Addresses written and the values written
    w_addr : List[Tuple[int, int]]
    # The symbolic semantics of instruction
    # None should be Register but I cannot find where it is imported from
    smt : List[Tuple[Union[None, MemoryAccess], str]]

    def __init__(self, eip : int, inst_type : InstructionType, r_regs : List[Tuple[str, int]], w_regs : List[Tuple[str, int]], \
                r_addr : List[Tuple[int, int]], w_addr : List[Tuple[int, int]], smt : List[str]):
        self.eip = eip
        self.inst_type = inst_type
        self.r_regs = r_regs
        self.w_regs = w_regs
        self.r_addr = r_addr
        self.w_addr = w_addr
        self.smt = smt

class FunctionInfo():
    ii : List[InstructionInfo]
    call_depth : int
    # TODO: unused as of now
    initial_memory : List[Tuple[int, int]]
    final_memory : List[Tuple[int, int]]
    # TODO: unused as of now
    inital_registers : List[Tuple[str, int]]
    final_registers : List[Tuple[str, int]]

    def __init__(self, ii : List[InstructionInfo], call_depth : int):
        self.ii = ii
        self.call_depth = call_depth
    
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
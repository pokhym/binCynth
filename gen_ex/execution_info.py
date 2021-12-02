from typing import List, Tuple

class InstructionInfo():
    # Which specific instruction is being executed
    eip : int
    # The registers read along with their values
    r_regs : List[Tuple[str, int]]
    # The registers written along with their values
    w_regs : List[Tuple[str, int]]
    # Addresses read and the value read
    r_addr : List[Tuple[int, int]]
    # Addresses written and the values written
    w_addr : List[Tuple[int, int]]
    # The symbolic semantics of instruction
    smt : List[str]

    def __init__(self, eip : int, r_regs : List[Tuple[str, int]], w_regs : List[Tuple[str, int]], \
                r_addr : List[Tuple[int, int]], w_addr : List[Tuple[int, int]], smt : List[str]):
        self.eip = eip
        self.r_regs = r_regs
        self.w_regs = w_regs
        self.r_addr = r_addr
        self.w_addr = w_addr
        self.smt = smt

class ExecutionInfo():
    ii : List[InstructionInfo]
    registers_touched : List[Tuple[str, int]]
    memory_touched : List[Tuple[str, int]]

    def __init__(self):
        ii = []

    def create_init_smt(self):
        """
            TODO: Create variables in SMT for the memory region used
                and all registers used
        """

    def create_final_assigment_smt(self):
        """
            TODO: Create the final SMT that states the final values
                of all the memory and 
        """

    def compose_smt(self):
        """
            TODO: Compose all SMT together
        """
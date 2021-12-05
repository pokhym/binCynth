from triton import TritonContext, ARCH
import lief

import subprocess

def freshCx() -> TritonContext:
    # Create context for x86
    cx = TritonContext(ARCH.X86_64)

    # Symbolic registers for rax and rbx
    rax = cx.symbolizeRegister(cx.registers.rax)
    #rbx = cx.symbolizeRegister(cx.registers.rbx)

    return cx

def gcc(fname: str, bname = "a.out") -> int:
    ret = subprocess.run(["gcc", fname, "-o", bname])
    return ret.returncode

def prefixZ3Def(prefix: str, z3Def: str): # -> (str, str)
    '''
    Prefix the identifier defined in a Z3 define-fun with the given prefix
    Returns the edited input string, and the edited symbolic variable
    '''
    l = z3Def.split(' ')
    l[1] = prefix + "_" + l[1]
    return ' '.join(l), l[1]

def loadBinary(cx: TritonContext, path: str): # -> (TritonContext, Int)
    '''
    Load a binary into our Triton context. I don't think we need the binary
    again, so I throw it away. 
    Returns the updated context and the entrypoint of the binary.
    '''
    binary = lief.parse(self.path)
    for phdr in binary.segments:
        size = phdr.physical_size
        vaddr = phdr.virtual_address
        cx.setConcreteMemoryAreaValue(vaddr, phdr.content)

    return (cx, binary.entrypoint)

def instructionsFrom(cx: TritonContext, pc: int): # -> [Instruction]
    '''
    Get the list of instructions from a binary loaded into Triton
    '''
    ret = []

    while pc:
        # Get opcode at current pc
        opCode = cx.getConcreteMemoryArea(pc, 16)

        # Create the instruction for the opcode
        instruction = Instruction()
        instruction.setAddress(pc)
        instruction.setOpCode(opCode)

        # Process in Triton -- Needed to update pc
        cx.processing(instruction)
        
        #print(instruction)

        # Put the instruction in our list
        ret.append(instruction)

        # End if halt is found
        if instruction.getType == OPCODE.X86.HLT:
            break

        pc = cx.getConcreteRegisterValue(cx.registers.rip)

    return ret

def toZ3(fname: str, bname: str, prefix: str): # (List[str], str)
    '''
    Returns a list of SMT definitions representing the execution of a file,
    and the last symbolic variable associated with the return register rax
    '''
    status = gcc(fname, bname)

    # Check that compilation succeeded
    if status != 0:
        print(f"Compilation of {fname}: {status}")
        exit()

    # Load the binary and get the Triton context and program counter
    cx, pc = loadBinary(freshCx(), bname)

    # Get the instructions
    instructions = instructionsFrom(cx, pc)

    # Get the Z3 definitions from instructions
    z3Defs = []
    raxSym = "!!!"
    for expression in inst.getSymbolicExpressions():
        z3Def, sym = prefaceZ3Def(prefix, str(expression)))
        z3Defs.append(z2Def)

        # If the expression's origin has rax in it
        if expression.getOrigin().find("rax") != -1:
            raxSym = sym

    # If the function doesn't have anything associated with the rax register
    if sym == "!!!":
        print("No symbolic variable for rax!")
        exit()

    return z3Defs, raxSym

def areEquivalentZ3(fname1: str, retSize1: int, 
                    fname2: str, retSize2: int): # -> List[str]
                    #bname1 = "bin1", bname2 = "bin2") -> bool:
    if retSize1 != retSize2:
        print("Different return values")
        return False
    else:
        # create an instruction list for a given file
        z3Defs1, rax1 = toZ3(fname1, bname1, bname1)
        z3Defs2, rax2 = toZ3(fname2, bname2, bname2)

        # Equivalence check
        z3Eq = f"(assert (= {rax1} {rax2}))"

        return z3Defs1 + z3Defs2 + [z3Eq]

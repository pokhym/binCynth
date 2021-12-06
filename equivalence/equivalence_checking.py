from triton import TritonContext, Instruction, ARCH, CPUSIZE, OPCODE
import lief

import subprocess

BASE_STACK = 0x9fffffff

def freshCx() -> TritonContext:
    # Create context for x86
    cx = TritonContext(ARCH.X86_64)

    # Symbolic registers
    for reg in cx.getAllRegisters():
        cx.setConcreteRegisterValue(reg, 0)

    # Defining a stack
    cx.setConcreteRegisterValue(cx.registers.rbp, BASE_STACK) # base pointer
    cx.setConcreteRegisterValue(cx.registers.rsp, BASE_STACK) # stack pointer
    # TODO: For now, assuming two arguments

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
    binary = lief.parse(path)
    for phdr in binary.segments:
        size = phdr.physical_size
        vaddr = phdr.virtual_address
        cx.setConcreteMemoryAreaValue(vaddr, phdr.content)

    #return (cx, binary.entrypoint.value)
    return (cx, binary.get_symbol('main').value)

def instructionsFrom(cx: TritonContext, pc: int): # -> [Instruction]
    '''
    Get the list of instructions from a binary loaded into Triton
    '''
    ret = []

    while pc:
        # Get opcode at current pc
        opcode = cx.getConcreteMemoryAreaValue(pc, 16)

        # Create the instruction for the opcode
        instruction = Instruction()
        instruction.setAddress(pc)
        instruction.setOpcode(opcode)

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

def getNameIfRegister(x) -> str:
    try:
        return x.getName()
    except AttributeError:
        return "MEM"

def toZ3(fname: str, bname: str, prefix: str): # -> (List[str], str, sym, sym)
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

    # Get the symbolic args
    bp = cx.getConcreteRegisterValue(cx.registers.rbp)
    arg1 = cx.getSymbolicMemory(bp - CPUSIZE.WORD)
    arg2 = cx.getSymbolicMemory(bp - 2 * CPUSIZE.WORD)

    # Get the instructions 
    instructions = instructionsFrom(cx, pc)

    # Get the Z3 definitions from instructions
    z3Defs = []
    raxSym = "!!!"
    for inst in instructions:
        for expression in inst.getSymbolicExpressions():
            z3Def, sym = prefixZ3Def(prefix, str(expression))
            z3Defs.append(z3Def)

            # If the expression's origin has eax in it
            origin = expression.getOrigin()
            name = getNameIfRegister(origin)
            if name == "rax":
                raxSym = sym

    # If the function doesn't have anything associated with the rax register
    if raxSym == "!!!":
        print("No symbolic variable for rax!")
        exit()

    return z3Defs, raxSym, arg1, arg2

def areEquivalentZ3(fname1: str, retSize1: int, 
                    fname2: str, retSize2: int,
                    bname1 = "bin1", bname2 = "bin2"): # -> [str]:
    if retSize1 != retSize2:
        print("Different return values")
        return False
    else:
        # create the z3 defs for a given file
        z3Defs1, eaxSym1, arg1Sym1, arg2Sym1 = toZ3(fname1, bname1, bname1)
        z3Defs2, eaxSym2, arg1Sym2, arg2Sym2 = toZ3(fname2, bname2, bname2)

        # TODO: Equivalence of input arguments
        # TODO: Symbolize all registers just in case
        # TODO: Create stack

        # Equality of arguments
        z3Arg1 = f"(assert (= {arg1Sym1} {arg1Sym2}))"
        z3Arg2 = f"(assert (= {arg2Sym1} {arg2Sym2}))"

        # Equivalence check -- MAY need to make this an implication, premised on equality of initial value of eax
        z3Eq = f"(assert (not (= {eaxSym1} {eaxSym2})))"

        return [z3Arg1, z3Arg2] + z3Defs1 + z3Defs2 + [z3Eq]


if __name__ == "__main__":
    xs = areEquivalentZ3("a.c", 1, "b.c", 1)
    for x in xs:
        print(x)


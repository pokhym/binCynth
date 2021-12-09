from os import chdir
import sys
sys.path.append("/usr/lib/python3.8/site-packages")
from triton import TritonContext, Instruction, ARCH, CPUSIZE, OPCODE, MemoryAccess
from typing import Tuple
import lief

import subprocess

BASE_STACK = 0x9fffffff

def freshCx(prefix: str) -> TritonContext:
    # Create context for x86
    cx = TritonContext(ARCH.X86_64)

    # Symbolic registers
    for reg in cx.getAllRegisters():
        if reg.getName() != "rbp" and reg.getName() != "rsp" and reg.getName() != "ebp" and reg.getName() != "esp" and reg.getName() != "eip" and reg.getName() != "rip":
            cx.symbolizeRegister(reg, f"{prefix}_{reg.getName()}")
        #cx.setConcreteRegisterValue(reg, 0) 
    # Defining a stack
    cx.setConcreteRegisterValue(cx.registers.rbp, BASE_STACK) # base pointer
    cx.setConcreteRegisterValue(cx.registers.rsp, BASE_STACK) # stack pointer
    # TODO: For now, assuming two arguments

    return cx

def gcc(fname: str, bname = "a.out") -> int:
    ret = subprocess.run(["gcc", fname, "-o", bname])
    return ret.returncode

def prefixZ3Def(prefix: str, z3Def: str) -> Tuple[str, str]:
    '''
    Prefix the identifier defined in a Z3 define-fun with the given prefix
    Returns the edited input string, and the edited symbolic variable
    '''
    z3Def = z3Def.replace("ref!", f"{prefix}_ref!")
    sym = z3Def.split(" ")[1]
    return z3Def, sym

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

def instructionsFrom(cx: TritonContext, pc: int, fname : str, prefix:str): # -> [Instruction, [sym]]
    '''
    Get the list of instructions from a binary loaded into Triton
    '''
    ret = []
    completed = 0

    while pc:
        # Get opcode at current pc
        opcode = cx.getConcreteMemoryAreaValue(pc, 16)

        # Create the instruction for the opcode
        instruction = Instruction()
        instruction.setAddress(pc)
        instruction.setOpcode(opcode)
        
        if completed == 3:
            rbp = cx.getRegister("rbp")
            rbpVal = cx.getConcreteRegisterValue(rbp)
            memArg1 = MemoryAccess(rbpVal - CPUSIZE.DWORD, CPUSIZE.DWORD)
            memArg1Sym = cx.symbolizeMemory(memArg1, f"{prefix}_{memArg1}_{CPUSIZE.DWORD}")
            #print("###", memArg1Sym, cx.getSymbolicExpression(memArg1Sym.getId()))
            memArg2 = MemoryAccess(rbpVal - CPUSIZE.DWORD * 2, CPUSIZE.DWORD)
            memArg2Sym = cx.symbolizeMemory(memArg1, f"{prefix}_{memArg2}_{2 * CPUSIZE.DWORD}")
            #print("###", memArg2Sym, memArg2Sym.getName(),cx.getSymbolicExpression(memArg1Sym.getId()))

        # Process in Triton -- Needed to update pc
        cx.processing(instruction)
        
        #print(instruction)
        #if str(instruction).find("dword ptr") != -1:

        # Put the instruction in our list
        ret.append(instruction)

        # End if halt is found
        if instruction.getType == OPCODE.X86.HLT:
            break
        # arg1 = cx.getSymbolicMemoryValue(BASE_STACK - CPUSIZE.DWORD)
        # arg2 = cx.getSymbolicMemoryValue(BASE_STACK - 2 * CPUSIZE.DWORD)


        pc = cx.getConcreteRegisterValue(cx.registers.rip)
        completed += 1

    #print("#########")
    return ret

def getNameIfRegister(x) -> str:
    try:
        return x.getName()
    except AttributeError:
        return "MEM"

def isSubstring(s1: str, s2: str) -> bool:
    return s1.find(s2) != -1

def expressionIsMovForReg(e, reg: str) -> bool:
    s = str(e)
    ret = isSubstring(s, "MOV operation") and isSubstring(s, f"mov {reg}")
    #print(ret, s)
    return ret

def toZ3(fname: str, bname: str, prefix: str): # -> (List[str], str, sym)
    '''
    Returns a list of SMT definitions representing the execution of a file,
    the last symbolic variable associated with the return register rax,
    and the symbolic variables representing the arguments
    '''
    status = gcc(fname, bname)

    # Check that compilation succeeded
    if status != 0:
        print(f"Compilation of {fname}: {status}")
        exit()

    # Load the binary and get the Triton context and program counter
    cx, pc = loadBinary(freshCx(prefix), bname)

    # Get the instructions and the symbolic memory for the args
    instructions = instructionsFrom(cx, pc, fname, prefix)

    # Get the Z3 definitions from instructions
    z3Defs = []
    raxSym = "!!!"
    arg1Sym = "!!!"
    arg2Sym = "!!!"
    functionCalled = False
    refNum = -1
    for inst in instructions:
        # Check if the first function call has occurred
        if not functionCalled and isSubstring(str(inst), "call"):
            #print("Function called")
            functionCalled = True

        for expression in inst.getSymbolicExpressions():
            z3Def, sym = prefixZ3Def(prefix, str(expression))
            z3Defs.append(z3Def)
            symRefNum = int(sym[9:])

            if refNum == -1:
                refNum = symRefNum
            assert refNum <= symRefNum
            while refNum < symRefNum:
                z3Defs.append(f"(declare-fun {prefix}_ref!{refNum} () (_ BitVec 8))")
                refNum += 1

            # If the expression's origin has eax in it
            origin = expression.getOrigin()
            name = getNameIfRegister(origin)
            if name == "rax":
                raxSym = sym

            # If the first function hasn't been called, then we may need to create a symbolic variable to refer to arg1
            if not functionCalled and expressionIsMovForReg(expression, "edi"):
                #print("Found arg")
                arg1Sym = f"{prefix}_arg1"
                z3Defs.append(f"(define-fun {arg1Sym} () (_ BitVec 64) {sym})")

            if not functionCalled and expressionIsMovForReg(expression, "esi"):
                arg2Sym = f"{prefix}_arg2"
                z3Defs.append(f"(define-fun {arg2Sym} () (_ BitVec 64) {sym})")

            refNum += 1

    # If the function doesn't have anything associated with the rax register
    if raxSym == "!!!":
        print("No symbolic variable for rax!")
        exit()

    # If no argument 1 has been found
    if arg1Sym == "!!!":
        print("No symbolic variable for arg1!")
        exit()

    # If no argument 1 has been found
    if arg2Sym == "!!!":
        print("No symbolic variable for arg2!")
#        exit()

    return z3Defs, raxSym, arg1Sym, arg2Sym

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
        z3Arg1Eq = f"(assert (= {arg1Sym1} {arg2Sym1}))"
        z3Arg2Eq = f"(assert (= {arg1Sym2} {arg2Sym2}))"

        # Equivalence check -- MAY need to make this an implication, premised on equality of initial value of eax
        z3Eq = f"(assert (not (= {eaxSym1} {eaxSym2})))"

        return z3Defs1 + z3Defs2 + [z3Arg1Eq, z3Arg2Eq, z3Eq, "(check-sat)"]

if __name__ == "__main__":
    # chdir("equivalence")
    file1 = input()
    file2 = input()
    xs = areEquivalentZ3(file1, 1, file2, 1)
    for x in xs:
        print(x)

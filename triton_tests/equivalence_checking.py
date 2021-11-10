from __future__ import print_function
import sys
# sys.path.insert(0, "/usr/lib/python3.8/site-packages")
from triton import *
import re


def append_prog_name_to_exp(sym_exp, prog_name):
    """
        returns a string for z3 given a triton SymbolicExpression
        where each ref is appended with the program name
    """
    smt2 = str(sym_exp)
    smt2 = smt2.replace("(define-fun ref", "(define-fun " + prog_name + "_ref")
    return smt2

def prog1(rep="z3"):
    """
        This program executes
            add rax, rbx
    """
    # Initialize Triton
    ctx = TritonContext()
    # Set to x86 with 64 Bits
    ctx.setArchitecture(ARCH.X86_64)
    # Print using PYTHON syntax default SMT2
    if rep != "z3":
        ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    # create symbolic registers for RAX and RBX
    rax = ctx.symbolizeRegister(ctx.registers.rax)
    rbx = ctx.symbolizeRegister(ctx.registers.rbx)

    # Note that RAX and RBX are equivalent of ref_0 and ref_1 as they were initialized that way
    print("RAX", rax, "RAX ID", "ref_" + str(rax.getId()))
    print("RBX", rbx, "RAX ID", "ref_" + str(rbx.getId()))

    # Create an instruction that begins at a specific address
    inst = Instruction()
    inst.setOpcode(b"\x48\x01\xD8") # add rax, rbx
    inst.setAddress(0x400000)
    inst2 = Instruction()
    inst2.setOpcode(b"\x48\x83\xc0\x00") # add rax, 0x0
    inst2.setAddress(0x400002)

    # Execute instruction
    ctx.processing(inst)

    # Print the instruction
    print(inst)

    # For everything that was updated in the instruction print the symbolic expresssions
    inst1_exp = []
    for expression in inst.getSymbolicExpressions():
        # print("\t", expression)
        inst1_exp.append([expression.getId(), expression.getOrigin(), str(expression)])

    return inst1_exp

def prog2(rep="z3"):
    """
        This program executs
            add rax, rbx
            add rax, 0
    """
    # Initialize Triton
    ctx = TritonContext()
    # Set to x86 with 64 Bits
    ctx.setArchitecture(ARCH.X86_64)
    # Print using PYTHON syntax default SMT2
    if rep != "z3":
        ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    # create symbolic registers for RAX and RBX
    rax = ctx.symbolizeRegister(ctx.registers.rax)
    rbx = ctx.symbolizeRegister(ctx.registers.rbx)

    # Note that RAX and RBX are equivalent of ref_0 and ref_1 as they were initialized that way
    print("RAX", rax, "RAX ID", "ref_" + str(rax.getId()))
    print("RBX", rbx, "RAX ID", "ref_" + str(rbx.getId()))

    # Create an instruction that begins at a specific address
    inst = Instruction()
    inst.setOpcode(b"\x48\x01\xD8") # add rax, rbx
    inst.setAddress(0x400000)
    inst2 = Instruction()
    inst2.setOpcode(b"\x48\x83\xc0\x00") # add rax, 0x0
    inst2.setAddress(0x400002)

    # Execute instruction
    ctx.processing(inst)

    # Print the instruction
    print(inst)

    # For everything that was updated in the instruction print the symbolic expresssions
    inst1_exp =  []
    for expression in inst.getSymbolicExpressions():
        # print("\t", expression)
        inst1_exp.append([expression.getId(), expression.getOrigin(), str(expression)])

    ctx.processing(inst2)
    print(inst2)
    inst2_exp = []
    for expression in inst2.getSymbolicExpressions():
        # print("\t", expression)
        inst2_exp.append([expression.getId(), expression.getOrigin(), str(expression)])

    return inst1_exp, inst2_exp

prog1_name = "prog1_"
_1_inst1_exp = prog1()
prog2_name = "prog2_"
_2_inst1_exp, _2_inst2_exp = prog2()
eq_check = []
eq_check_id = 0

print("#### ####")

for i1 in _1_inst1_exp:
    for i2 in _2_inst2_exp:
        if i1[1].getId() == i2[1].getId() and (i1[1].getId() == 0 or i1[1].getId() == 1):
            print(i1[1].getId())
            print('\t', i1[0])
            print('\t', i1[1])
            print('\t', i1[2])
            print('\t', "####")
            print(i2[1].getId())
            print('\t', i2[0])
            print('\t', i2[1])
            print('\t', i2[2])
            _1_refname = re.findall(r"ref![0-9]+", i1[2])
            assert len(_1_refname) >= 1
            _1_refname = _1_refname[0]
            _2_refname = re.findall(r"ref![0-9]+", i2[2])
            assert len(_1_refname) >= 1
            _2_refname = _2_refname[0]
            eq_check.append("(define-fun eq_" + str(eq_check_id) + " () Bool" + "(= " + prog1_name + _1_refname + " " + prog2_name + _2_refname +")" + ")\n")
            eq_check_id += 1
for i1 in _1_inst1_exp:
    i1[2] = i1[2].replace("ref!", prog1_name+ "ref!")
for i1 in _2_inst1_exp:
    i1[2] = i1[2].replace("ref!", prog2_name+ "ref!")
for i1 in _2_inst2_exp:
    i1[2] = i1[2].replace("ref!", prog2_name+ "ref!")


with open("equivalence_checking.smt2", "w") as fd:
    # create the initial variables for registers rax and rbx for both programs
    # then assert they must be equal
    rax_init = "(declare-fun rax_init () (_ BitVec 64))\n"
    rbx_init ="(declare-fun rbx_init () (_ BitVec 64))\n"
    prog1_rax_init = "(declare-fun prog1_ref!0 () (_ BitVec 64))\n"
    prog1_rbx_init = "(declare-fun prog1_ref!1 () (_ BitVec 64))\n"
    prog2_rax_init = "(declare-fun prog2_ref!0 () (_ BitVec 64))\n"
    prog2_rbx_init = "(declare-fun prog2_ref!1 () (_ BitVec 64))\n"
    prog1_rax_shared = "(define-fun prog1_rax_shared () Bool (= rax_init prog1_ref!0))\n"
    prog1_rbx_shared = "(define-fun prog1_rbx_shared () Bool (= rbx_init prog1_ref!1))\n"
    prog2_rax_shared = "(define-fun prog2_rax_shared () Bool (= rax_init prog2_ref!0))\n"
    prog2_rbx_shared = "(define-fun prog2_rbx_shared () Bool (= rbx_init prog2_ref!1))\n"
    fd.write(rax_init)
    fd.write(rbx_init)
    fd.write(prog1_rax_init)
    fd.write(prog1_rbx_init)
    fd.write(prog2_rax_init)
    fd.write(prog2_rbx_init)
    fd.write(prog1_rax_shared)
    fd.write(prog1_rbx_shared)
    fd.write(prog2_rax_shared)
    fd.write(prog2_rbx_shared)

    # insert all the constraints for all instructions of both programs
    for i in _1_inst1_exp:
        fd.write(str(i[2]))
        fd.write("\n")
    for i in _2_inst1_exp:
        fd.write(str(i[2]))
        fd.write("\n")
    for i in _2_inst2_exp:
        fd.write(str(i[2]))
        fd.write("\n")

    for i in range(eq_check_id):
        fd.write(eq_check[i])

    # write the assertions
    # this is a validity check where we are checking the not to ensure the "not equivalent" never happens
    assertion = "(assert (not (=> (and prog1_rax_shared prog1_rbx_shared prog2_rax_shared prog2_rbx_shared) (and "
    for i in range(eq_check_id):
        assertion += "eq_" + str(i)
    assertion += "))))"
    fd.write(assertion)

    fd.close()
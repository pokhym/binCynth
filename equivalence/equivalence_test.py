from __future__ import print_function
import sys
from typing import Dict, List, Tuple, final
sys.path.insert(0, "/usr/lib/python3.8/site-packages")
import subprocess
import logging

from triton     import TritonContext, ARCH, Instruction, MemoryAccess, CPUSIZE, OPCODE, MODE

import re

# info only
logging.basicConfig(level=logging.INFO)

def load_binary(ctx, prog_path):
    import lief

    # Map the binary into the memory
    binary = lief.parse(prog_path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        logging.debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)

    return binary

def emulate(ctx, pc, prog_id):
    call_count = 0
    ret_count = 0
    sym_exp = []
    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        ctx.processing(instruction)

        # Display instruction
        logging.debug(instruction)

        # Display symbolic expressions
        for expr in instruction.getSymbolicExpressions():
            logging.debug('\t' + str(expr))
            expr = str(expr).replace("ref!", "_" + str(prog_id) + "_" + "ref!")
            expr = expr.replace("SymVar", "_" + str(prog_id) + "_" + "SymVar")
            sym_exp.append(expr)

        
        if instruction.getType() == OPCODE.X86.CALL:
            call_count += 1
        elif instruction.getType() == OPCODE.X86.RET:
            ret_count += 1
        elif instruction.getType() == OPCODE.X86.HLT:
            break

        if call_count + 1 == ret_count:
            break

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    return sym_exp

def display_info(ctx, prog_id : int):
    # reg_name -> define-fun
    reg_dict : Dict[str : str] = {}
    # addr -> define-fun
    memory_dict : Dict[int : str]= {}
    # reg_name -> ast-expr
    final_dict : Dict[str : str] = {}
    logging.debug("")
    logging.debug('Symbolic registers information')
    logging.debug('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
    # (Reference ID, Original Register Enumeration)
    ref_to_reg_enum : List[Tuple[int, int]] = []
    for k, v in list(ctx.getSymbolicRegisters().items()):
        logging.debug(str(v.getId()) + " " + str(v))
        ref_to_reg_enum.append((v.getId(), k))
    ref_to_reg_enum.sort(key=lambda x: x[0])
    for rore in ref_to_reg_enum:
        try:
            v = ctx.getSymbolicRegisters()[rore[1]]
            logging.debug(str(ctx.getRegister(rore[1]).getName()) + " " + str(v))
            reg_name = ctx.getRegister(rore[1]).getName()
            # (define-fun ref!8 () (_ BitVec 1) SymVar_8)
            def_fun = str(v)
            # (define-fun ref!8 () (_ BitVec 1) _0_SymVar_8)
            def_fun = def_fun.replace("SymVar", "_" + str(prog_id) + "_SymVar")
            # # (declare-fun _0_SymVar8 () (_ BitVec 1))
            # declare_fun = ""
            # if "SymVar" in def_fun:
            #     declare_fun = "(declare-fun _" + str(prog_id) + "_" + str(v.getAst()) + " () (_ BitVec " + str(v.getAst().getBitvectorSize()) + "))"
            reg_dict.update({reg_name : def_fun})
        except:
            logging.info("Register: " + str(ctx.getRegister(rore[1])) + " is not symbolized")

    logging.debug("")
    logging.debug('Symbolic memory information')
    logging.debug('~~~~~~~~~~~~~~~~~~~~~~~~~~~')
    for k, v in list(ctx.getSymbolicMemory().items()):
        logging.debug(hex(k) + " " + str(v))
        addr = k
        def_fun = str(v)
        def_fun = def_fun.replace("SymVar", "_" + str(prog_id) + "_SymVar")
        memory_dict.update({addr : def_fun})

    logging.debug("")
    logging.debug('Craft symbolic stuffs')
    logging.debug('~~~~~~~~~~~~~~~~~~~~~')
    eax  = ctx.getRegisterAst(ctx.registers.eax)
    rax  = ctx.getRegisterAst(ctx.registers.rax)
    logging.debug('Register EAX:' + str(eax))
    logging.debug('Register RAX: ' + str(rax))
    # (define-fun _0_final_eax () (_ BitVec 32))
    eax_def_fun = "(define-fun _" + str(prog_id) + "_final_eax () (_ BitVec 32)" + str(eax) + ")"
    eax_def_fun.replace("ref!", "_" + str(prog_id) + "_" + "ref!")
    final_dict.update({"eax" : eax_def_fun.replace("ref!", "_" + str(prog_id) + "_" + "ref!")})
    final_dict.update({"rax" : "(define-fun _" + str(prog_id) + "_final_rax () (_ BitVec 64)" + str(rax) + ")"})

    return reg_dict, memory_dict, final_dict

def symbolize_registers(ctx, prog_id):
    sym_var_reg : List[str] = []
    # symbolize anything that isnt rbp and rsp
    for reg in ctx.getAllRegisters():
        if reg.getName() != 'rbp' and reg.getName() != 'rsp' and reg.getName() != 'ebp' \
                    and reg.getName() != 'esp' and reg.getName() != 'rip' and reg.getName() != 'eip':
            sr = ctx.symbolizeRegister(reg)
            declare_fun = "(declare-fun _" + str(prog_id) + "_" + str(sr.getName()) + " () (_ BitVec " + str(sr.getBitSize()) + "))"
            sym_var_reg.append(declare_fun)
            define_fun = str(ctx.getSymbolicExpression(sr.getId()))
            define_fun = define_fun.replace("SymVar", "_" + str(prog_id) +"_SymVar")
            define_fun = define_fun.replace("ref!", "_" + str(prog_id) + "_ref!")
            sym_var_reg.append(define_fun)
    return sym_var_reg

def symbolize_memory(ctx, prog_id):
    sym_var_mem : List[str] = []
    for i in range(0x100):
        mem = MemoryAccess(ctx.getConcreteRegisterValue(ctx.getRegister('rbp')) - i * CPUSIZE.DWORD, CPUSIZE.DWORD)
        a = ctx.symbolizeMemory(mem)
        identifier = ctx.getSymbolicExpression(a.getId())
        logging.debug(str(ctx.getMemoryAst(mem)))
        logging.debug(str(a))
        logging.debug("")
        declare_fun = "(declare-fun _" + str(prog_id) + "_" + str(a.getName()) + " () (_ BitVec " + str(a.getBitSize()) + "))"
        sym_var_mem.append(declare_fun)
        def_fun = str(ctx.getSymbolicExpression(a.getId()))
        def_fun = def_fun.replace("SymVar", "_" + str(prog_id) + "_SymVar")
        def_fun = def_fun.replace("ref!", "_" + str(prog_id) + "_ref!")
        sym_var_mem.append(def_fun)
    return sym_var_mem

def get_init_cond(sym_var_reg_0, sym_var_mem_0, sym_var_reg_1, sym_var_mem_1):
    init_cond = []
    init_cond.append("(define-fun init-cond () Bool (and ")

    for svr0, svr1 in zip(sym_var_reg_0, sym_var_reg_1):
        if "define-fun" in svr0 and "define-fun" in svr1:
            refs_0 = re.findall(r"_0_ref![0-9]+", svr0)
            refs_1 = re.findall(r"_1_ref![0-9]+", svr1)
            assert(len(refs_0) >= 1)
            assert(len(refs_1) >= 1)
            init_cond.append("\t(= " + refs_0[0] + " " + refs_1[0] +  ")")
    for svm0, svm1 in zip(sym_var_mem_0, sym_var_mem_1):
        if "define-fun" in svm0 and "define-fun" in svm1:
            refs_0 = re.findall(r"_0_ref![0-9]+", svm0)
            refs_1 = re.findall(r"_1_ref![0-9]+", svm1)
            assert(len(refs_0) >= 1)
            assert(len(refs_1) >= 1)
            init_cond.append("\t(= " + refs_0[0] + " " + refs_1[0] +  ")")
    init_cond.append("))")

    return init_cond

def create_assertion():
    return """
(assert
    (not
        (=>
            init-cond
            (= _0_final_eax _1_final_eax)
        )
    )
)
(check-sat)
    """
#     return """
# (assert
#     (not
#         (and
#             (=>
#                 init-cond
#                 (not (= _0_final_eax _1_final_eax))
#             )
#             (=>
#                 (= _0_final_eax _1_final_eax)
#                 init-cond
#             )
#         )
#     )
# )
# (check-sat)
# """


def create_z3(output_z3_path, sym_var_reg_0, sym_var_mem_0, inst_sym_0_expr, final_dict_0, sym_var_reg_1, sym_var_mem_1, inst_sym_1_expr, final_dict_1):
    """
        List[str]
        sym_var_reg_0

        List[str]
        sym_var_mem_0

        List[str]
        inst_sym_expr

        reg_name -> (declare-fun, define-fun)
        reg_dict : Dict[str : Tuple[str, str]] = {}

        addr -> define-fun
        memory_dict : Dict[int : str] = {}

        reg_name -> ast-expr
        final_dict : Dict[str : str] = {}
    """
    output_0 : List[str] = []
    output_0.append("; 0 REG SYM DEFS")
    for svr0 in sym_var_reg_0:
        output_0.append(svr0)
    output_0.append("; 0 MEMORY SYM DEFS")
    for svm0 in sym_var_mem_0:
        output_0.append(svm0)

    output_0.append("; 0 INSTRS")
    for is0e in inst_sym_0_expr:
        output_0.append(str(is0e))    
    
    # Dump final EAX/RAX
    # TODO: Assuming only EAX
    output_0.append("; 0 FINAL REGISTERS")
    output_0.append("; eax")
    output_0.append(final_dict_0["eax"])

    # Join together into string
    output_0_str = "\n".join(output_0)

    ################################

    output_1 : List[str] = []
    output_1.append("; 1 REG SYM DEFS")
    for svr1 in sym_var_reg_1:
        output_1.append(svr1)
    output_1.append("; 0 MEMORY SYM DEFS")
    for svm1 in sym_var_mem_1:
        output_1.append(svm1)

    output_1.append("; 1 INSTRS")
    for is1e in inst_sym_1_expr:
        output_1.append(str(is1e))    
    
    # Dump final EAX/RAX
    # TODO: Assuming only EAX
    output_1.append("; 1 FINAL REGISTERS")
    output_1.append("; eax")
    output_1.append(final_dict_1["eax"])

    ################################
    init_cond = get_init_cond(sym_var_reg_0, sym_var_mem_0, sym_var_reg_1, sym_var_mem_1)

    # Join together into string
    output_0_str = "\n".join(output_0)
    output_1_str = "\n".join(output_1)
    init_cond_str = "\n".join(init_cond)
    assertion = create_assertion()
    output = output_0_str + "\n\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n" + output_1_str \
        + "\n\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n" + init_cond_str \
        + "\n\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n" + assertion

    with open(output_z3_path, "w") as fd:
        fd.write(output)
        fd.close()
    

def equivalence_check_run(binary_0_path, binary_1_path, output_z3_path):
    # set up triton context
    ctx_0 = TritonContext()
    ctx_0.setArchitecture(ARCH.X86_64)
    ctx_0.setMode(MODE.ALIGNED_MEMORY, True)

    # clear everything
    ctx_0.concretizeAllMemory()
    ctx_0.concretizeAllRegister()
    binary_0 = load_binary(ctx_0, binary_0_path)
    
    # set ebp and rsp
    ctx_0.setConcreteRegisterValue(ctx_0.registers.rbp, 0x7fffffff)
    ctx_0.setConcreteRegisterValue(ctx_0.registers.rsp, 0x7fffffff)

    # symbolize registers
    sym_var_reg_0 : List[str] = symbolize_registers(ctx_0, 0)

    # symbolize memory
    sym_var_mem_0 : List[str] = symbolize_memory(ctx_0, 0)

    # emulate
    inst_sym_0_expr = emulate(ctx_0, binary_0.get_symbol('main').value, 0)

    reg_dict_0, memory_dict_0, final_dict_0 = display_info(ctx_0, 0)

    # clear everything
    # set up triton context
    ctx_1 = TritonContext()
    ctx_1.setArchitecture(ARCH.X86_64)
    ctx_1.setMode(MODE.ALIGNED_MEMORY, True)
    ctx_1.concretizeAllMemory()
    ctx_1.concretizeAllRegister()
    binary_1 = load_binary(ctx_1, binary_1_path)
    ctx_1.setConcreteRegisterValue(ctx_1.registers.rbp, 0x7fffffff)
    ctx_1.setConcreteRegisterValue(ctx_1.registers.rsp, 0x7fffffff)
    # symbolize registers
    sym_var_reg_1 : List[str] = symbolize_registers(ctx_1, 1)

    # symbolize memory
    sym_var_mem_1 : List[str] = symbolize_memory(ctx_1, 1)

    # emulate
    inst_sym_1_expr = emulate(ctx_1, binary_1.get_symbol('main').value, 1)

    reg_dict_1, memory_dict_1, final_dict_1 = display_info(ctx_1, 1)

    create_z3(output_z3_path, sym_var_reg_0, sym_var_mem_0, inst_sym_0_expr, final_dict_0, sym_var_reg_1, sym_var_mem_1, inst_sym_1_expr, final_dict_1)


if __name__ == '__main__':
    equivalence_check_run("/home/user/pysynth/tests/c/equivalent1_1", "/home/user/pysynth/tests/c/equivalent2_1", "/home/user/pysynth/equivalence/out")
    print("This should be unsat")
    subprocess.run(["z3", "-smt2", "/home/user/pysynth/equivalence/out"], capture_output=False)
    
    equivalence_check_run("/home/user/pysynth/tests/c/equivalent1_2", "/home/user/pysynth/tests/c/equivalent2_2", "/home/user/pysynth/equivalence/out")
    print("This should be unsat")
    subprocess.run(["z3", "-smt2", "/home/user/pysynth/equivalence/out"], capture_output=False)

    equivalence_check_run("/home/user/pysynth/tests/c/different1_1", "/home/user/pysynth/tests/c/different2_1", "/home/user/pysynth/equivalence/out")
    print("This should be sat")
    subprocess.run(["z3", "-smt2", "/home/user/pysynth/equivalence/out"], capture_output=False)

    equivalence_check_run("/home/user/pysynth/tests/c/different1_2", "/home/user/pysynth/tests/c/different2_2", "/home/user/pysynth/equivalence/out")
    print("This should be sat")
    subprocess.run(["z3", "-smt2", "/home/user/pysynth/equivalence/out"], capture_output=False)

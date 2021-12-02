import sys
import os.path
import unicorn as uni
from unicorn.x86_const import *
import capstone as cap
from unicorn.unicorn_const import UC_ARCH_X86

"""
    FILE GLOBALS
"""
FILE_NAME = "[func_extraction.py]"
BINARY = bytearray()

"""
    CAPSTONE GLOBALS
"""
cap_instance = cap.Cs(cap.CS_ARCH_X86, cap.CS_MODE_64)

"""
    UNICORN GLOBALS
"""
# Offset into ELF to begin execution
ELF_START = 0x1000
# memory address where emulation starts
ADDRESS = 0x0000000
# size of memory
MEMORY_SIZE = 512 * 1024 * 1024 # 2MB

def print_error(func_name: str, err: str):
    print(FILE_NAME, func_name, err)

def load_binary(bin_path: str):
    global BINARY
    func_name: str = "{load_binary}"
    if not os.path.exists(bin_path):
        print_error(func_name, "binary does not exist")
    
    with open(bin_path, "rb") as fd:
        BINARY += fd.read()

### UNICORN CODE ###

# callback for tracing basic blocks
def hook_block(uc, address, size, user_data):
    print(">>> Tracing basic block at 0x%x, block size = 0x%x" %(address, size))

# callback for tracing instructions
def hook_code(uc, address, size, user_data):
    print(">>> Tracing instruction at 0x%x, instruction size = 0x%x" %(address, size))
    eflags = uc.reg_read(UC_X86_REG_EFLAGS)
    print(">>> --- EFLAGS is 0x%x" %eflags)

def hook_code64(uc, address, size, user_data):
    print(">>> Tracing instruction at 0x%x, instruction size = 0x%x" %(address, size))
    rip = uc.reg_read(UC_X86_REG_RIP)
    print(">>> RIP is 0x%x" %rip);

    mem=uc.mem_read(address, size)
    for (address, size, mnemonic, op_str) in cap_instance.disasm_lite(mem, address):
        print("0x%x:\t%s\t%s" %(address, mnemonic, op_str))
        print("##\t", mem)


def execute_binary():
    global BINARY
    # initalize Unicorn
    mu = uni.Uc(UC_ARCH_X86, uni.UC_MODE_64)
    # Map memory
    mu.mem_map(ADDRESS, MEMORY_SIZE)
    # write machine code to be emulated to memory
    #  BINARY = b"\xf3\x0f\x1e\xfa"
    mu.mem_write(ADDRESS, bytes(BINARY))
    # mu.mem_write(ADDRESS, bytes(BINARY))
    # initialize regs
    mu.reg_write(UC_X86_REG_RAX, 0x0)
    mu.reg_write(UC_X86_REG_RBX, 0x0)
    mu.reg_write(UC_X86_REG_RCX, 0x0)
    mu.reg_write(UC_X86_REG_RDX, 0x0)
    mu.reg_write(UC_X86_REG_RSI, 0x0)
    mu.reg_write(UC_X86_REG_RDI, 0x0)
    mu.reg_write(UC_X86_REG_R8, 0x0)
    mu.reg_write(UC_X86_REG_R9, 0x0)
    mu.reg_write(UC_X86_REG_R10, 0x0)
    mu.reg_write(UC_X86_REG_R11, 0x0)
    mu.reg_write(UC_X86_REG_R12, 0x0)
    mu.reg_write(UC_X86_REG_R13, 0x0)
    mu.reg_write(UC_X86_REG_R14, 0x0)
    mu.reg_write(UC_X86_REG_R15, 0x0)
    # mu.reg_write(UC_X86_REG_RAX, 0x71f3029efd49d41d)
    # mu.reg_write(UC_X86_REG_RBX, 0xd87b45277f133ddb)
    # mu.reg_write(UC_X86_REG_RCX, 0xab40d1ffd8afc461)
    # mu.reg_write(UC_X86_REG_RDX, 0x919317b4a733f01)
    # mu.reg_write(UC_X86_REG_RSI, 0x4c24e753a17ea358)
    # mu.reg_write(UC_X86_REG_RDI, 0xe509a57d2571ce96)
    # mu.reg_write(UC_X86_REG_R8, 0xea5b108cc2b9ab1f)
    # mu.reg_write(UC_X86_REG_R9, 0x19ec097c8eb618c1)
    # mu.reg_write(UC_X86_REG_R10, 0xec45774f00c5f682)
    # mu.reg_write(UC_X86_REG_R11, 0xe17e9dbec8c074aa)
    # mu.reg_write(UC_X86_REG_R12, 0x80f86a8dc0f6d457)
    # mu.reg_write(UC_X86_REG_R13, 0x48288ca5671c5492)
    # mu.reg_write(UC_X86_REG_R14, 0x595f72f6e4017f6e)
    # mu.reg_write(UC_X86_REG_R15, 0x1efd97aea331cccc)

    # setup stack
    mu.reg_write(UC_X86_REG_RSP, ADDRESS + 0x200000)

    # tracing all basic blocks with customized callback
    mu.hook_add(uni.UC_HOOK_BLOCK, hook_block)

    # tracing all instructions in range [ADDRESS, ADDRESS+20]
    mu.hook_add(uni.UC_HOOK_CODE, hook_code64, None, ADDRESS, ADDRESS+20)

    rax = mu.reg_read(UC_X86_REG_RAX)
    rbx = mu.reg_read(UC_X86_REG_RBX)
    rcx = mu.reg_read(UC_X86_REG_RCX)
    rdx = mu.reg_read(UC_X86_REG_RDX)
    rsi = mu.reg_read(UC_X86_REG_RSI)
    rdi = mu.reg_read(UC_X86_REG_RDI)
    r8 = mu.reg_read(UC_X86_REG_R8)
    r9 = mu.reg_read(UC_X86_REG_R9)
    r10 = mu.reg_read(UC_X86_REG_R10)
    r11 = mu.reg_read(UC_X86_REG_R11)
    r12 = mu.reg_read(UC_X86_REG_R12)
    r13 = mu.reg_read(UC_X86_REG_R13)
    r14 = mu.reg_read(UC_X86_REG_R14)
    r15 = mu.reg_read(UC_X86_REG_R15)

    print(">>> RAX = 0x%x" %rax)
    print(">>> RBX = 0x%x" %rbx)
    print(">>> RCX = 0x%x" %rcx)
    print(">>> RDX = 0x%x" %rdx)
    print(">>> RSI = 0x%x" %rsi)
    print(">>> RDI = 0x%x" %rdi)
    print(">>> R8 = 0x%x" %r8)
    print(">>> R9 = 0x%x" %r9)
    print(">>> R10 = 0x%x" %r10)
    print(">>> R11 = 0x%x" %r11)
    print(">>> R12 = 0x%x" %r12)
    print(">>> R13 = 0x%x" %r13)
    print(">>> R14 = 0x%x" %r14)
    print(">>> R15 = 0x%x" %r15)
    try:
        mu.emu_start(ADDRESS + 0x40, ADDRESS + 0x80)
        a = 0
    except Exception as e:
        print("UNICORN ERROR: %s " % e)
    # try:
    #     mu.emu_start(ADDRESS + 0x40, ADDRESS +0x40 + len(BINARY))
    # except uni.UcError as e:
    #     print("UNICORN ERROR: %s" % e)
    
    # now print out some registers
    print(">>> Emulation done. Below is the CPU context")

    rax = mu.reg_read(UC_X86_REG_RAX)
    rbx = mu.reg_read(UC_X86_REG_RBX)
    rcx = mu.reg_read(UC_X86_REG_RCX)
    rdx = mu.reg_read(UC_X86_REG_RDX)
    rsi = mu.reg_read(UC_X86_REG_RSI)
    rdi = mu.reg_read(UC_X86_REG_RDI)
    r8 = mu.reg_read(UC_X86_REG_R8)
    r9 = mu.reg_read(UC_X86_REG_R9)
    r10 = mu.reg_read(UC_X86_REG_R10)
    r11 = mu.reg_read(UC_X86_REG_R11)
    r12 = mu.reg_read(UC_X86_REG_R12)
    r13 = mu.reg_read(UC_X86_REG_R13)
    r14 = mu.reg_read(UC_X86_REG_R14)
    r15 = mu.reg_read(UC_X86_REG_R15)

    print(">>> RAX = 0x%x" %rax)
    print(">>> RBX = 0x%x" %rbx)
    print(">>> RCX = 0x%x" %rcx)
    print(">>> RDX = 0x%x" %rdx)
    print(">>> RSI = 0x%x" %rsi)
    print(">>> RDI = 0x%x" %rdi)
    print(">>> R8 = 0x%x" %r8)
    print(">>> R9 = 0x%x" %r9)
    print(">>> R10 = 0x%x" %r10)
    print(">>> R11 = 0x%x" %r11)
    print(">>> R12 = 0x%x" %r12)
    print(">>> R13 = 0x%x" %r13)
    print(">>> R14 = 0x%x" %r14)
    print(">>> R15 = 0x%x" %r15)


if __name__ == "__main__":
    try:
        load_binary(sys.argv[1])
    except Exception as e:
        print(e)
        exit(0)
    try:
        execute_binary()
    except Exception as e:
        print(e)
        exit(0)
# gen_ex

This folder contains two different components

1. Function Extraction
2. Example Generation

These two components will allow us to break down a binary into smaller parts and allow synthesis to be tractable as we will only be operating on small sections at a time.

We will use `Triton` (`https://github.com/JonathanSalwan/Triton`) as a CPU emulator to emulate the program and get the input output values.
This is based on `unicorn` (`unicorn` (`https://github.com/unicorn-engine/unicorn/`) which in tuern is based upon QEMU.

From this, we will extract

1. The registers read and written per instruction + values
2. The memory addresses read and written per instruction + values
3. The semantics of the program by dumping the SMT2


Using scripts from `afl-unicorn` (`https://github.com/Battelle/afl-unicorn`) we are also able to easily load and dump state from 

## Function
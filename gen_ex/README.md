# gen_ex

This folder contains two different components

1. Function Extraction
2. Example Generation

These two components will allow us to break down a binary into smaller parts and allow synthesis to be tractable as we will only be operating on small sections at a time.

We will use `Triton` (`https://github.com/JonathanSalwan/Triton`) as a CPU emulator to emulate the program and get the input output values.
<!-- This is based on `unicorn` (`unicorn` (`https://github.com/unicorn-engine/unicorn/`) which in tuern is based upon QEMU. -->

Additionall we also use `lief` (`https://lief-project.github.io/`) to easily process ELF binaries for Linux systems.

From this, we will extract

1. The registers read and written per instruction + values
2. The memory addresses read and written per instruction + values
3. The semantics of the program by dumping the SMT2

With this information we are then able to extract the input output examples of a function call to some binary.

Currently we assume the x86 System-V calling convention with ELF binaries.
Moreover we also assume a specifific input program to be given.

**NOTE**: Currently only supporting integer programs.

## Required Inputs

1. An input binary with a black box API call
2. A list of input examples (see `tests/python/triton_examples.py` for an example)

## The Input Examples

Input examples, will need to be generated manually and have the following form

```
int32,5,int32,6,
```

This represents 2 `int` argument inputs of value 5 and 6 to an API function.

## The Input Binary

We assume a user has a library binary which can be imported in their C code via an include.
From there they can use API functions from those functions to get a return value or modify some memory.

As such we require the user to write their own wrapper `main` function which calls the desired API call for which they do not have the source code.

```C
#include "blackbox_binary.hpp"

int main(){
    int a;
    int b;
    return api_call(a, b);
}
```

`int a, b` are the input functions to the API call.
These values will be filled in by Triton to setup the stack call to `api_call(a,b)`.

The `FunctionExtractor` will then return dictionary of input output examples for each binary which was called from within.


<!-- Using scripts from `afl-unicorn` (`https://github.com/Battelle/afl-unicorn`) we are also able to easily load and dump state from  -->

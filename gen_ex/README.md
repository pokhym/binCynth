# gen_ex

This folder contains two different components

1. Function Extraction
2. Example Generation

These two components will allow us to break down a binary into smaller parts and allow synthesis to be tractable as we will only be operating on small sections at a time.

We will use `unicorn` (`https://github.com/unicorn-engine/unicorn/`) as a CPU emulator to emulate the program and get the input output values.

Furthermore, we will be able to observe directly the instructions being executed without the downsides of static binary analysis.
As such we we use some heuristics to extract the functions called.

Using scripts from `afl-unicorn` (`https://github.com/Battelle/afl-unicorn`) we are also able to easily load and dump state from 

## Function
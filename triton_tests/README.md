# triton-tests

This document contains information about the import files here and things that need to be done in order to fully get Triton to do what we want

## Files

Only files of note will be listed here

* `recover_semantics.py`: An example of how we can recover the semantics of one instruction

## Things to Look into

* `TritonContext().symbolizeMemory()`: Symbolic memory representation?
* Obtaining the whole AST tree and reursively printing everything?
* Script to convert the ref_N into a SMT2 Z3 file so we can obtain the semantics as a conjunction?
    * Maybe just use the Python representation?
* Create two equivalent cases and check equivalence
    * add rax rbx, add rax, 0
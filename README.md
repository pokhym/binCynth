# pysynth
Recovering semantics of black box programs

## Symbolic Execution Ideas

### angr

Angr allows one to initialize variables of specific types and then add constraints and evaluate and solve the constraint

https://docs.angr.io/core-concepts/solver

Therefore the idea could be to

1. Insert initializations for variables
2. Read a program line by line and add constraints
3. Save the state of the program as a formula by the end of the program
4. For each test input (I) and output (O) assign the inputs to the input variables and evaluate the formula
5. Check if the evaluated value is equivalent to O.  If it does, then this formula is equivalent to the semantics of the program
6. Repeat for all inputs and outputs.

Not sure if angr is able to create a counter example for us to place back into the CEGIS loop

### CrossHair

https://crosshair.readthedocs.io/en/latest/index.html

Not sure how to get any symbolic equation out of it, it is able to return counterexamples though.
It operates like Dafny where functions are provided with pre/post and those are checked.

### KLEE

Pivot to using LLVM to perform the symbolic execution.

Use Cython to convert Python code to C and then call the C functions from a new Python function via C types?

# pysynth

Synthesizing black boxed library functions via symbolic execution and component based synthesis.
This has been tested on Ubuntu 20.04 LTS.

## What This Tool Provides

In this project we provide a tool which synthesizes functions which can be called from a binary blob.

It takes the following input

1. A binary
2. Input examples for a specific library function call
3. A wrapper to call our library function

And produces the following output

1. Synthesized C functions in the form of SSA components

## An Example

Suppose we wish to synthesize the following C function `modify_stuff`, it also uses another function `modify_stuff2` which the user is unaware of.

```C
int modify_stuff2(int a){
    return a + 1;
}
int modify_stuff(int a, int b){
    a = modify_stuff2(a);
    return 2 * modify_stuff2(a) + b;
}
```

The user will then generate input output examples by calling `modify_stuff` on their own.
The user is assumed to know the input types and return types of the library function `modify_stuff`
An example text file will look like the following.

```
int32,52,int32,86,
int32,27,int32,95,
int32,3,int32,21,
...
```

This is a CSV where all even columns represent the input type, and the odd columns will represent the value.

After that the user will write an additional wrapper function for our synthesis engine to analyze.
The input variables to the library call do not need to be initialized our tool will do that for the user during analysis.

```C
#include "modify_stuff.h"
int main(){
  int a;
  int b;
  return modify_stuff(a, b);
}
```

After compiling this wrapper, run `main.py`.
It will prompt the user for the location of the examples, and the binary to analyze.
Synthesized functions will be placed in `synth_engine/components.cpp`.

```C
int synthed_4(int in_1){
	int out_0 = int_add(1, in_1);
	return out_0;
}
int synthed_5(int in_1,int in_2){
	int out_0 = int_add(4, in_2);
	int out_1 = int_add(in_1, out_0);
	int out_2 = int_add(in_1, out_1);
	return out_2;
}

```
## Dependencies

We use the symbolic engine Triton (`https://github.com/JonathanSalwan/Triton`).
Please follow the install instructions to install it on your system.

Additionally, please make sure to install the newest version of Capstone (`https://github.com/aquynh/capstone`).
The version found on package managers may be out of date (it is on Ubuntu 20.04 LTS)

## Files and Folders

### Root

`main.py` is the wrapper to all the components of the system.

### equivalence

This folder contains files relating to the equivalence checking of 2 binaries.

1. `equivalence/equivalence_test.py`

### gen_ex

This folder contains files relating to the generation of examples from the binary we wish to synthesize functions from.

1. `gen_ex/execution_info.py`: Stores the information of each function during execution
2. `gen_ex/func_extraction.py`: Contains the FunctionExtractor class
3. `gen_ex/io_example.py`: Contains a class representing an IO example for the binary we wish to synthesize functions from

### synth_engine

This folder contains the files for the `synth_engine`

1. `synth_engine/component_state.cpp/hpp`: Contains the ComponentState class which stores the different permuations of a component we wish to test
2. `synth_engine/components.cpp/hpp`: Components and constants relating to how we treat components
3. `synth_engine/engine.cpp/hpp`: Contains the Engine class which is the synthesis engine and other functions such as example parsing.
4. `synth_engine/main.cpp`: The main level call to the Engine
5. `synth_engine/synth_state.cpp/hpp`: Contains the SynthState class which represents a choice of components to use.
  This is then further used to execute the components and determine if they match the input output examples.

### tests

This folder contains some tests that were used in development.
One can think of them as examples.

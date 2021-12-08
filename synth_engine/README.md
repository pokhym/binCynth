# synth_engine

This folder contains the synthesis engine we will be using and the information on how to store the components used in synthesis.

## Why C++?

This allows us to store our components as straight C/C++ code and combine them together algorithmically in our synthesis engine without making multiple execve calls to both the compiler and compiled executable everytime we wish to change the ordering of the components.

## Files

1. `synth_engine/component_state.cpp/hpp`: Contains the ComponentState class which stores the different permuations of a component we wish to test
2. `synth_engine/components.cpp/hpp`: Components and constants relating to how we treat components
3. `synth_engine/engine.cpp/hpp`: Contains the Engine class which is the synthesis engine and other functions such as example parsing.
4. `synth_engine/main.cpp`: The main level call to the Engine
5. `synth_engine/synth_state.cpp/hpp`: Contains the SynthState class which represents a choice of components to use.
  This is then further used to execute the components and determine if they match the input output examples.

## TODO

* components
    * Convert `FUNCS` in components to be vectors so we can actually update them without actually re-executing stuff
* engine
    * Synthesis engine needs support for 3 arg/4 arg functions
    * add_component
* comments and documentation on files some of it is out of date
# synth_engine

This folder contains the synthesis engine we will be using and the information on how to store the components used in synthesis.

## Why C++?

This allows us to store our components as straight C/C++ code and combine them together algorithmically in our synthesis engine without making multiple execve calls to both the compiler and compiled executable everytime we wish to change the ordering of the components.

## Files

* `component_state.cpp/hpp` : State of each component we are using
* `components.cpp/hpp` : The components that we are actually using
* `engine.hpp/cpp`: Engine code
* `main.cpp`: Wrapper code
* `Makefile`: Makefile

## TODO

* components
    * Convert `FUNCS` in components to be vectors so we can actually update them without actually re-executing stuff
* engine
    * Synthesis engine needs support for 1 arg/3 arg/4 arg functions
    * add_component
* comments and documentation on files some of it is out of date
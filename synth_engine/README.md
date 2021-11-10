# synth_engine

This folder contains the synthesis engine we will be using and the information on how to store the components used in synthesis.

## Why C++?

This allows us to store our components as straight C/C++ code and combine them together algorithmically in our synthesis engine without making multiple execve calls to both the compiler and compiled executable everytime we wish to change the ordering of the components.

## Files

* `engine.hpp/cpp`: Engine code
* `main.cpp`: Wrapper code
* `Makefile`: Makefile
#ifndef SYNTH_STATE_H
#define SYNTH_STATE_H

#include <iostream>
#include <map>
#include <vector>
#include "component_state.hpp"
#include "util.cpp"

/**
 * @brief SynthState
 *  This class stores the complete synthesis state for N instructions.
 *  As such this means that it will store all permutations of possible function/component orderings
 *  and their input output arguments.
 * 
 *  Each function/component state will be stored within the ComponentState class
 */
class SynthState{
    public:
        /******* VARIABLES ********/
        // The number of input arguments the program we are synthesizing will use
        int num_input_arguments;
        // This version of a 3 function program uses components 0, 1, and 2 in that order
        // "0,1,2" : [ComponentState0, ComponentState1, ComponentState2],
        // This version of a 3 function program uses components 0, 1, and 2 in that order
        // "2,1,15" : [ComponentState2, ComponentState1, ComponentState15],
        std::vector<int> function_choice; 
        std::vector<ComponentState *> component_state;

        /****** FUNCTIONS *******/
        SynthState(std::vector<int> function_choice, int num_input_arguments);
        ~SynthState();

        void synth_state_dump();
};

#endif // SYNTH_STATE_H
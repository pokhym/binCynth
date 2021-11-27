#ifndef SYNTH_STATE_H
#define SYNTH_STATE_H

#include <iostream>
#include <map>
#include <vector>
#include <cmath>
#include "component_state.hpp"
#include "util.cpp"
#include "components.hpp"

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

        // Contains a vector of indices into FUNCS in components.hpp
        // This version of a 3 function program uses components 0, 1, and 2 in that order
        // function_choice = [0, 1, 2]
        // This version of a 3 function program uses components 2, 15, and 0 in that order
        // function_choice = [2, 15, 0]
        std::vector<int> function_choice; 
        // Index 0 of function_choice corresponds to index 0 of component_state.
        //  function_choice[0] = 2
        //  component_state[0] = ComponentState for FUNC[2]
        std::vector<ComponentState *> component_state;
        // store a map containig a mapping between const_id and a ComponentState pointer
        std::map<int, uint64_t> const_to_cs;

        /****** FUNCTIONS *******/
        SynthState(std::vector<int> function_choice, int num_input_arguments);
        ~SynthState();

        void synth_state_dump();

        /**
         * @brief evaluate : Evaluate a sets of input output conditions and return true or false if they
         *  match the examples input. Wraps evaluate_helper
         * 
         * @param examples : A vector of i/o examples
         * @return true true : If true, we were able to successfully execute all examples to match
         *  the current SynthState and perm
         * @return false : Failed to match all examples
         */
        bool evaluate(std::vector<std::map<int, uint64_t> *> * examples);

        /**
         * @brief get_synthesized_function : Upon successfully synthesizing a function call this
         *  to return a C version of the function. It will also print the functions and args used.
         * 
         * @return std::string 
         */
        std::string get_synthesized_function();
    
    private:
        // Initialized to false, if this is set to true at any point we have successfully synthesized
        // a function that matches all our examples
        bool synthesized;
        
        // Iterators for keeping track of how far we have recursed into function choices
        std::vector<int>::iterator function_choice_it;
        std::vector<int>::iterator function_choice_it_end;

        // permuation vector containing the current set of input output conditions we are evaluating
        // the 0th index corresponds to the 0th function choice, the 1st index corresponds to the 1st function choice
        // and so on
        std::vector<std::vector<int>> perm;
        
        /**
         * @brief evaluate_helper : A helper function that recursively enumerates all combinations of ComponentState I/O
         *  to be executed
         * 
         * @param examples : A vector of i/o examples
         * @param func_idx : An index to which function we are processing. It is < function_choice
         * @return true true : If true, we were able to successfully execute all examples to match
         *  the current SynthState and perm
         * @return false : Failed to match all examples
         */
        bool evaluate_helper(std::vector<std::map<int, uint64_t> *> * examples
                                // , std::vector<std::vector<int>> perm
                                , int func_idx);
        
        /**
         * @brief execute : Actually executes a set of i/o arguments
         * 
         * @param examples : A vector of i/o examples
         * @return true : If true, we were able to successfully execute all examples to match
         *  the current SynthState and perm
         * @return false : Failed to match all examples
         */
        bool execute(std::vector<std::map<int, uint64_t> *> * examples);

        /**
         * @brief create_io : Creates a map of input/output to be used by execute. It is stored in ret.
         *  This initialization function will clear ret and only initialize the input variables in the map.
         *  Additionally it will also return a uint64_t which represents the output of the example
         * 
         * @param example : An input example
         * @param ret : A map
         *      key: Negative if input
         *      value: The input value
         * @return uint64_t : Output of the example
         */
        uint64_t create_io(std::map<int, uint64_t> * example, std::map<int, uint64_t> * ret);
};

#endif // SYNTH_STATE_H
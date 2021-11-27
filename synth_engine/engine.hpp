#ifndef ENGINE_H
#define ENGINE_H

#include <string>
#include <vector>
#include <map>
#include <set>
#include <tuple>
#include <algorithm>
// #include "component_state.hpp"
#include "synth_state.hpp"
#include "components.hpp"
#include "util.cpp"

enum InOut {IO_IN, IO_OUT};
enum Types {TYPE_INT};

class Engine {
    public:
        /***** PUBLIC VARIABLES ******/
        // Maximum number of instructions the synthesized program may have
        int max_instrs;
        // Number of input arguments to the function we are trying to synthesize
        int num_input_arguments;
        // Path relative to the synth engine executable containing a binary
        std::string path_to_binary;
        // Path relative to a CSV file containing IO examples
        std::string path_to_examples;
        // How we delimit each part of an example
        std::string example_delimiter;
        // The word we use to mark a specific example argument as output
        std::string out_delimiter;
        // The word we use to mark a specific example argument as input
        std::string in_delimiter;
        // The word we use to mark a specific example argument as an integer
        std::string int_delimiter;
        // A vector containing each example.
        // Each entry is a dictionary laid out as follows.
        //      key: integer
        //      val: uint64_t
        // For an input variable the key will be IO_IN - some_int
        //      IO_IN due to the enum will be 0, we will subtract -1, -2, -3 and so on
        // For an output variable the key will be IO_OUT
        //      IO_OUT due to the enum will always be 1
        std::vector<std::map<int, uint64_t> *> examples;

        // This stores all permutations of specific instruction orderings and their
        // corresponding IO argument combinations.
        // The key represents the choice of function/component orderings we choose
        //      "0,1,2": Choode component id 0, 1, 2 in that order
        //      "2,1,15": Choose component id 2, 1, 15 in that order
        // The value represents a SynthState object for all the permutations of IO orderings between
        // these choices of compoonents and their orderings
        std::map<std::vector<int>, SynthState *> synth_state;

        /***** PUBLIC FUNCTIONS ******/
        /**
         * @brief Construct a new Engine object
         */
        Engine(std::string path_to_binary, std::string path_to_examples, int max_instrs);
        /**
         * @brief Destroy the Engine object
         */
        ~Engine();

        /**
         * @brief load_components : Loads the database of information
         * 
         * @returns bool : True if load was successful False otherwise
         */
        bool load_components();

        /**
         * @brief load_test_cases : Loads up the IO examples which we want to synthesize for
         * 
         * @return true 
         * @return false 
         */
        bool load_test_cases();

        /**
         * @brief prep_synth : Prepares a binary to be synthesized
         *  generates fuzzing information to get input output examples
         * 
         * @returns int
         *  0 : successful
         *  -1 : error (unable to find binary)
         */
        int prep_synth(std::string path_to_binary);

        /**
         * @brief synth : Synthesize a function given a set of components to use
         */
        void synth();

        /**
         * @brief verify : Verify that a synthesized function actually matches 
         *  all our input/output examples
         * @returns SynthState * : This is NULL if we were unable to synthesize something that verifies
         *  all examples.  Otherwise this will not be NULL
         */
        SynthState * verify();

        /**
         * @brief debrittle : Generate a verified p_dash which is different 
         *  from the input p. Check that p == p_dash semantically
         */
        void debrittle();

        /**
         * @brief add_component : Add a verified component to our ground truth set
         */
        void add_component();

        /**
         * @brief dump_examples : Prints all the examples we parsed
         */
        void dump_exmaples();
    
    private:
        /**
         * @brief update_examples : Updates our examples
         * 
         * @param ex 
         */
        void update_examples(std::vector<std::string> ex);

        /**
         * @brief clear_synth_state : Deletes the SynthState object
         * 
         */
        void clear_synth_state();

        /**
         * @brief choose_func : Chooses a function to for the id-th component we wish to
         *  add to our synthesized program
         * 
         * @param num_instr_to_choose : The number of components (functions) we wish to use
         */
        void choose_func(int num_instr_to_choose);

        /**
         * @brief dump_synthesized_function
         * 
         * @param ss : A SynthState pointer to the SynthState that correctly verifies
         */
        void dump_synthesized_function(SynthState * ss);
};

#endif // ENGINE_H
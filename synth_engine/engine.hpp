#ifndef ENGINE_H
#define ENGINE_H

#include <string>
#include <vector>
#include <tuple>
#include "components.hpp"

enum InOut {IO_IN, IO_OUT};
enum Types {TYPE_INT};

class Engine {
    public:
        /***** PUBLIC VARIABLES ******/
        std::string path_to_binary;
        std::string path_to_examples;
        std::string example_delimiter;
        std::string out_delimiter;
        std::string in_delimiter;
        std::string int_delimiter;
        std::vector<std::vector<std::tuple<int, int, uint64_t>>> examples;

        /***** PUBLIC FUNCTIONS ******/
        /**
         * @brief Construct a new Engine object
         */
        Engine(std::string path_to_binary, std::string path_to_examples);
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
         * @returns bool : True if verifiation succeeds else false
         */
        bool verify();

        /**
         * @brief debrittle : Generate a verified p_dash which is different 
         *  from the input p. Check that p == p_dash semantically
         */
        void debrittle();

        /**
         * @brief add_component : Add a verified component to our ground truth set
         */
        void add_component();
    
    private:
        /**
         * @brief update_examples : Updates our examples
         * 
         * @param ex 
         */
        void update_examples(std::vector<std::string> ex);
};

#endif // ENGINE_H
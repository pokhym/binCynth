#ifndef ENGINE_H
#define ENGINE_H

#include <string>
#include "components.hpp"

class Engine {
    public:
        Engine();
        ~Engine();
        /**
         * @brief load_components : Loads the database of information
         * 
         * @returns bool : True if load was successful False otherwise
         */
        bool load_components();

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
};

#endif // ENGINE_H
#ifndef COMPONENT_STATE_H
#define COMPONENT_STATE_H

#include <map>
#include <set>
#include <tuple>
#include <vector>
#include <cmath>
#include "components.hpp"

enum ComponentStateEnum {
    COMP_TYPE,
    N_IAGRS,
    N_OARGS,
    IN_ID,
    IN_ID_PERM,
    OUT_ID
};

class ComponentState{
    public:
        /***** VARIABLES ******/
        int comp_type;                              // Component identifier
        int func_choice_id;                         // The i-th function in the synthesized function
        int n_iargs;                                // Number of inputs for that component
        int n_oargs;                                // Number of outputs for that component
        std::set<int> in_id;                        // The identifiers of the possible input arguments
                                                    //  negative numbers represent original input arguments to
                                                    //  the whole program
                                                    // If we are trying to synthesize func(int a, int b)
                                                    //  b = -1, a = -2 just like a traditional x86 calling convention
                                                    // Any numbers < -2 will represent the constants
                                                    // To account for constants we just need to store additional negative numbers
                                                    // the offset calculation is as follows
                                                    //     -1 * (func_choice_id + 1) * max_num_iargs - constant_id  - 1
                                                    // Therefore for a synthesized function with 1 ACTUAL input argument and
                                                    // max_num_iargs as 3 with one 2 input function (comp_type 1) and
                                                    // one 3 input function (comp_type 2) we would have
                                                    //  2 input func : -1, -4, -5
                                                    //  3 input func : -1, -7, -8, -9
                                                    // 3 actual input args, max_num_iargs 3, 3 input function (comp_type 2) and
                                                    // 2 input function (comp_type 1)
                                                    //  3 input func: -1, -2, -3, -4, -5, -6
                                                    //  2 input func: -1, -2, -3, -7, -8
        std::map<int, uint64_t> const_map;          // Stores a map between a constant identifier and the value to use
                                                    // when executing
        // TODO: Currently assuming that we only have up to 2 input arguments for a function
        std::set<std::vector<int>> in_id_perm; // The permudation of input argument identifiers
        int out_id; // The output argument identifier

        /***** FUNCTIONS *****/
        ComponentState();
        ~ComponentState();

        /**
         * @brief create_constant_iarg : Returns a constant iarg identifier for input i
         * 
         * @param i : An integer representing the iarg number
         * @param offset : An offset from -1 * pow(2, CONST_MAX_BIT) representing the constant value
         * @return int : The calculated constant identifier
         */
        int create_constant_iarg(int offset);

        /**
         * @brief is_constant_iarg : Checks if the in_id is a constant
         * 
         * @param i 
         * @return true : Is a constant
         * @return false : Is not a constant
         */
        bool is_constant_iarg(int in_id);
};

#endif // COMPONENT_STATE_H
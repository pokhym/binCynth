#ifndef COMPONENT_STATE_H
#define COMPONENT_STATE_H

#include <set>
#include <tuple>

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
        int n_iargs;                                // Number of inputs for that component
        int n_oargs;                                // Number of outputs for that component
        std::set<int> in_id;                        // The identifiers of the possible input arguments
                                                    //  negative numbers represent original input arguments to
                                                    //  the whole program
                                                    // If we are trying to synthesize func(int a, int b)
                                                    //  b = -1, a = -2 just like a traditional x86 calling convention
                                                    // Any numbers < -2 will represent the constants
                                                    // TODO: HOW TO STORE CONSTANTS
        // TODO: Currently assuming that we only have up to 2 input arguments for a function
        std::set<std::tuple<int, int>> in_id_perm; // The permudation of input argument identifiers
        int out_id; // The output argument identifier

        /***** FUNCTIONS *****/
        ComponentState();
        ~ComponentState();
};

#endif // COMPONENT_STATE_H
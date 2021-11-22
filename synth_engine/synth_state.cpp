#include "synth_state.hpp"

SynthState::SynthState(std::vector<int> function_choice, int num_input_arguments){
    this->function_choice = function_choice;
    this->num_input_arguments = num_input_arguments;
    
    bool first = true;
    int max_input_args = 0;
    // assign len(function_choice) components into component_state
    for(int idx = 0 ; idx < (this->function_choice).size() ; idx++){
        ComponentState * cs = new ComponentState();
        this->component_state.push_back(cs);
        cs->comp_type = this->function_choice[idx];
        cs->n_iargs = FUNCS_NUM_IARGS[this->function_choice[idx]];
        cs->n_oargs = FUNCS_NUM_OARGS[this->function_choice[idx]];
        
        // in_id should at the very least contain the input arguments
        // determine the maximum number of input arguments to this function
        for(int i = 0 ; i < this->num_input_arguments ; i++)
            cs->in_id.insert(-1 * (i + 1));
        // First function will not have any other possible input arguments
        if(first){
            first = false;
        }
        else{
            // add additional input arguments from previous functions
            for(int prev_idx = idx - 1 ; prev_idx >= 0; prev_idx--)
                cs->in_id.insert(prev_idx);
        }

        // out_id is the same as the index of the function
        cs->out_id = idx;
    }

    // generate the permuations of input arguments for each component
    for(ComponentState * c : this->component_state){
        std::vector<std::vector<int>> ret;
        std::vector<int> in_id_vec(c->in_id.begin(), c->in_id.end());
        // get combinations
        ret = nCk(c->in_id.size(), c->n_iargs);
        // generate permutations
        for(std::vector<int> comb : ret){
            do {
                // create a vector for the permutation
                std::vector<int> perm;
                for(auto ele : comb){
                    perm.push_back(in_id_vec[ele]);
                }
                // insert the permutation
                c->in_id_perm.insert(perm);
            } while(std::next_permutation(comb.begin(), comb.end()));
        } 
    }

}

SynthState::~SynthState(){
    for(auto cs : this->component_state)
        delete cs;
}

void SynthState::synth_state_dump(){
    std::cout << "\tSYNTH STATE FUNCTION_CHOICE:" << std::endl;
    // std::cout << "\t\t";
    for(int f : this->function_choice){
        std::cout << "\t\t";
        std::cout << "func_choice: " <<  f << std::endl;
        for(ComponentState * cs : this->component_state){
            if(cs->comp_type == f){
                std::cout << "\t\tcomp_state:" << cs->comp_type << std::endl;
                for(std::vector<int> ipv : cs->in_id_perm){
                    std::cout << "\t\t\t";
                    for(int ipe : ipv){
                        std:: cout << ipe << " ";
                    }
                    std::cout << std::endl;
                }
            }
        }
    }
    std::cout << std::endl;
}
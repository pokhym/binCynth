#include "synth_state.hpp"

#define SYNTH_STATE_DEBUG 1
#undef SYNTH_STATE_DEBUG

/*** PUBLIC ***/

SynthState::SynthState(std::vector<int> function_choice, int num_input_arguments){
    this->function_choice = function_choice;
    this->num_input_arguments = num_input_arguments;
    this->synthesized = false;
    this->num_constants = 0;
    this->max_constants = 0;

    this->const_id_to_cs.clear();
    this->const_num_to_cs.clear();
    
    bool first = true;
    
    // assign len(function_choice) components into component_state
    for(int idx = 0 ; idx < (int)(this->function_choice).size() ; idx++){
        ComponentState * cs = new ComponentState();
        this->component_state.push_back(cs);
        cs->comp_type = this->function_choice[idx];
        cs->func_choice_id = idx;
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

    // // generate the permuations of input arguments for each component
    // for(ComponentState * c : this->component_state){
    //     std::vector<std::vector<int>> ret;
    //     std::vector<int> in_id_vec(c->in_id.begin(), c->in_id.end());
    //     // get combinations
    //     ret = nCk(c->in_id.size(), c->n_iargs);
    //     // generate permutations
    //     for(std::vector<int> comb : ret){
    //         do {
    //             // create a vector for the permutation
    //             std::vector<int> perm;
    //             for(auto ele : comb){
    //                 perm.push_back(in_id_vec[ele]);
    //             }
    //             // insert the permutation
    //             c->in_id_perm.insert(perm);
    //         } while(std::next_permutation(comb.begin(), comb.end()));
    //     } 
    // }

    // update the maximum number of constants
    for(int idx = 0 ; idx < (int)(this->function_choice).size() ; idx++){
        this->max_constants += this->component_state[idx]->n_iargs;
        for(int i = 0 ; i < this->component_state[idx]->n_iargs ; i++)
            this->const_num_to_cs.insert({i, this->component_state[idx]});
        // determine if we need to add any constants by default
        if(this->component_state[idx]->n_iargs > this->num_input_arguments){
            if(this->component_state[idx]->n_iargs - this->num_input_arguments > this->num_constants)
                this->num_constants = this->component_state[idx]->n_iargs - this->num_input_arguments;
        }
    }
    
    this->update_constants(false);
    // // attempt to use 0 constants first
    // if(!this->update_constants(false)){
    //     // otherwise incrementally add constants
    //     while(this->num_constants < this->max_constants){
    //         if(this->update_constants(true))
    //             break;
    //     }   
    // }

}

SynthState::~SynthState(){
    for(auto cs : this->component_state)
        delete cs;
}

bool SynthState::update_constants(bool increment_constant_count){
    if(increment_constant_count)
        this->num_constants++;
    
    // default case if there aree 0 constants
    if(this->num_constants == 0){
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
        return true;
    }

    std::vector<std::vector<int>> constant_combs = nCk(this->max_constants, this->num_constants);
    std::cout << "constant_combs " << constant_combs.size() << std::endl;
    for(ComponentState * c : this->component_state){
        c->in_id_perm.clear();
        c->in_id.clear();
    }

    // regenerate the permuations of input arguments for each component
    // for each combination of constants
    for(std::vector<int> const_comb : constant_combs){
        for(ComponentState * c : this->component_state){
            // clear the in_id_perm/in_id first
            // c->in_id_perm.clear();
            // c->in_id.clear();

            // re-insert default in_ids
            for(int i = 0 ; i < this->num_input_arguments ; i++)
                c->in_id.insert(-1 * (i + 1));
            
            std::vector<std::vector<int>> ret;
            std::vector<int> in_id_vec(c->in_id.begin(), c->in_id.end());

            // if the const_comb contains constants for this current ComponentState
            // add it to the in_id_vec
            for(int cc : const_comb){
                if(this->const_num_to_cs[cc] == c){
                    // in_id_vec.push_back(c->c);
                    std::cout << "cc " << cc << std::endl;
                    for(int offset = 0 ; offset < 2 * pow(2, CONST_MAX_BIT) ; offset++){
                        int const_id = c->create_constant_iarg(offset);
                        this->const_id_to_cs.insert({const_id, c->const_map[const_id]});
                        c->in_id.insert(const_id);
                        in_id_vec.push_back(const_id);
                    }
                }
            }

            // get combinations
            ret = nCk(c->in_id.size(), c->n_iargs);
            // generate permutations
            for(std::vector<int> comb : ret){
                do {
                    // create a vector for the permutation
                    std::vector<int> perm;
                    for(auto ele : comb){
                        // if(ele >= in_id_vec.size()){
                        //     std::cout << "AAAAAAAAA" << std::endl;
                        //     return false;
                        // }
                        perm.push_back(in_id_vec[ele]);
                    }
                    // insert the permutation
                    c->in_id_perm.insert(perm);
                } while(std::next_permutation(comb.begin(), comb.end()));
            } 
        }
    }
    return true;
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

bool SynthState::evaluate(std::vector<std::map<int, uint64_t> *> * examples){

    this->function_choice_it = this->function_choice.begin(); // function counter iterator
    this->function_choice_it_end = this->function_choice.end(); // function counter iterator
    
    // initialize empty vector of input choices
    // std::vector<std::vector<int>> perm;
    perm.clear();
    // make recursive call here
    // perm.push_back(*this->component_state[0]->in_id_perm.begin());
    evaluate_helper(examples
        // , this->perm 
        , 0);
    
    return this->synthesized;
}

std::string SynthState::get_synthesized_function(){
    std::string synth_c;
    synth_c += "#include \"components.hpp\"\n\n";

    synth_c += "int synthed(";
    for(int i = this->num_input_arguments ; i > 0 ; i--){
        if(i == 1){
            synth_c += "int in_" + std::to_string(i) + "){\n";
        }
        else{
            synth_c += "int in_" + std::to_string(i) + ","; 
        }
    }

    std::cout << "Functions Used:" << std::endl;
    for(int idx = 0 ; idx < (int)this->function_choice.size() ; idx++){
        std::cout << "\t" << FUNC_NAMES[this->function_choice[idx]] << std::endl;

        synth_c += "\tint out_" + std::to_string(idx) + " = " + FUNC_NAMES[this->function_choice[idx]] + "(";
        
        std::cout << "\t\t" << "With Arguments: ";
        // std::cout << "\t\t" << std::endl;
        for(int args_idx = 0 ; args_idx < this->perm[idx].size() ; args_idx++){
            if(args_idx == this->perm[idx].size() - 1){
                if(this->perm[idx][args_idx] < 0){
                    if(this->const_id_to_cs.count(this->perm[idx][args_idx]) != 0){
                        // TODO: THIS IS CURRENTLY ONLY INTEGERS
                        synth_c += std::to_string((int)this->const_id_to_cs[this->perm[idx][args_idx]]) + ");\n";
                    }
                    else
                        synth_c += "in_" + std::to_string(-1 * this->perm[idx][args_idx]) + ");\n";
                }
                else
                    synth_c += "out_" + std::to_string(this->perm[idx][args_idx]) + ");\n";
            }
            else{
                if(this->perm[idx][args_idx] < 0){
                    if(this->const_id_to_cs.count(this->perm[idx][args_idx]) != 0){
                        // TODO: THIS IS CURRENTLY ONLY INTEGERS
                        synth_c += std::to_string((int)this->const_id_to_cs[this->perm[idx][args_idx]]) + ", ";
                    }
                    else
                        synth_c += "in_" + std::to_string(-1 * this->perm[idx][args_idx]) + ", ";    
                }
                else{
                    synth_c += "out_" + std::to_string(this->perm[idx][args_idx]) + ", ";
                }
            }
            std::cout << this->perm[idx][args_idx] << " ";
        }
        std::cout << std::endl;
    }
    synth_c += "\treturn out_" + std::to_string(this->function_choice.size() - 1) + ";\n}";
    
    return synth_c;
}

/*** PRIVATE ***/

bool SynthState::evaluate_helper(std::vector<std::map<int, uint64_t> *> * examples
                                // , std::vector<std::vector<int>> perm
                                , int func_idx)
{
    // if we have successfully synthesized quit
    if(this->synthesized)
        return this->synthesized;

    // termination condition where we have reached the last function that we wish to add
    // to our synthesized function
    if(this->function_choice_it == this->function_choice_it_end){
        // execute here as we now have a complete set of i/o choices
#ifdef SYNTH_STATE_DEBUG
        std::cout << "PERMS " << func_idx << ":\n";
        for(std::vector<int> ele : this->perm){
            std::cout << "\t";
            for(int elee : ele){
                std::cout << elee << " "; 
            }
            std::cout << std::endl;
        }
        std::cout << std::endl;
#endif

        // perform execution
        this->synthesized = execute(examples);

        return this->synthesized;
    }

    std::set<std::vector<int>>::iterator curr_in_id_perm_it = this->component_state[func_idx]->in_id_perm.begin();
    std::set<std::vector<int>>::iterator next_in_id_perm_it;
    if(func_idx + 1 < (int)this->function_choice.size()){
        next_in_id_perm_it = this->component_state[func_idx + 1]->in_id_perm.begin();
    }

    while(curr_in_id_perm_it != this->component_state[func_idx]->in_id_perm.end() && this->synthesized == false){

#ifdef SYNTH_STATE_DEBUG
        std::vector<int> a = *curr_in_id_perm_it;
        std::cout << "func_idx: " << func_idx << ", curr_in_id_perm_it: ";
        for(auto b : a){
            std::cout << b << " ";
        }
        std::cout << std::endl;
#endif

        perm.push_back(*curr_in_id_perm_it);
        this->function_choice_it++; // increment iterator for recursive call
        evaluate_helper(examples
            // , perm
            , func_idx + 1);
        if(this->synthesized)
            return this->synthesized;
        this->function_choice_it--;
        perm.pop_back();

        curr_in_id_perm_it++;
    }
    return this->synthesized;
}

bool SynthState::execute(std::vector<std::map<int, uint64_t> *> * examples){
    // double check we can actually execute first
    for(int func_idx = 0; func_idx < (int)this->function_choice.size() ; func_idx++){
        // check the number of input arguments matches
        if((int)this->perm[func_idx].size() != FUNCS_NUM_IARGS[func_idx]){
            return false; // terminate if not true
        }
    }

    // create dict for storing the execution results
    std::map<int, uint64_t> * io = new std::map<int, uint64_t>();
    // create uint64_t for storing output value
    uint64_t out;
    // create a var for func choice size
    int num_funcs = this->function_choice.size();
    for(std::map<int, uint64_t> * m : *examples){
        out = this->create_io(m, io);

#ifdef SYNTH_STATE_DEBUG
        std::cout << "Out: " << out << std::endl;
        std::cout << "In :";
        for(auto asdf = io->begin() ; asdf != io->end() ; asdf ++){
            std::cout << asdf->first << ":" << asdf->second << " ";
        }
        std::cout << std::endl;
#endif

        // loop through function choice and update the io dict as we go
        for(int func_idx = 0 ; func_idx < num_funcs ; func_idx++){
            switch(this->perm[func_idx].size()){
                case 1:{
                    std::cout << "ERROR: Unimplemented function input size of 1" << std::endl;
                    delete io;
                    return false;
                    break;
                }
                case 2:{
                    // initialize a return variable
                    uint64_t ret = 0;
                    // execute the component
                    ret = FUNCS[this->function_choice[func_idx]](io->at(this->perm[func_idx][0]), io->at(this->perm[func_idx][1]));
#ifdef SYNTH_STATE_DEBUG
                    std::cout << "Executing func: " << this->function_choice[func_idx] << " " << FUNC_NAMES[this->function_choice[func_idx]] << ", args: "<< io->at(this->perm[func_idx][0]) << " " << io->at(this->perm[func_idx][1]) << ", Return value: " << ret << std::endl;
#endif
                    // update the io
                    io->insert({func_idx, ret});
                    break;
                }
                default:{
                    std::cout << "ERROR: Invalid function input size" << std::endl;
                    delete io;
                    return false;
                    break;
                }
            }
        }
#ifdef SYNTH_STATE_DEBUG
        // dump the result map
        std::cout << "Dumping Result map" << std::endl;
        for(auto it = io->begin() ; it != io->end() ; it++){
            std::cout << "\t" << it->first << " " << it->second << std::endl;
        }
#endif
        // not all io examples matched
        if(io->at(num_funcs - 1) != out){
            delete io;
            return false;
        }
    }

#ifdef SYNTH_STATE_DEBUG
    std::cout << "SYNTH_STATE: Found winning synthesized function" << std::endl;
#endif

    delete io;
    return true;
}

uint64_t SynthState::create_io(std::map<int, uint64_t> * example, std::map<int, uint64_t> * ret){
    uint64_t out = 0;
    // clear return dictionary first as we will use it multiple times
    ret->clear();
    std::map<int, uint64_t>::iterator it;
    for (it = example->begin(); it != example->end(); it++) {
        // input
        if(it->first < 0){
            ret->insert({it->first, it->second});
        }
        else{
            out = it->second;
        }
    }
    // TODO: FIX THIS IS VERY SLOW
    // additionally add all constants 
    std::map<int, uint64_t>::iterator const_it;
    for(const_it = this->const_id_to_cs.begin() ; const_it != this->const_id_to_cs.end() ; const_it++){
        ret->insert({const_it->first, const_it->second});
    }
    return out;
}
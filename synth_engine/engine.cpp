#include <iostream>
#include <fstream>
#include <sstream>
#include "engine.hpp"
#include "components.hpp"


#ifndef ENGINE_DEBUG
#define ENGINE_DEBUG 1
#endif

/*** PUBLIC ***/

Engine::Engine(std::string path_to_binary, std::string path_to_examples, int max_instrs){
    std::cout <<"Initializing Engine stuff..." << std::endl;
    this->path_to_binary = path_to_binary;
    this->path_to_examples = path_to_examples;
    this->example_delimiter = ",";
    this->out_delimiter = "out";
    this->in_delimiter = "in";
    this->int_delimiter = "int";
    this->target_synth_count = new int(2);
    this->current_synth_count = new int(0);

    this->max_instrs = max_instrs;
    this->num_input_arguments = -1;

     if (FILE *file = fopen(this->path_to_examples.c_str(), "r")) {
        fclose(file);
        std::cout << "Examples were found at " << this->path_to_examples <<std::endl;
    } else {
        std::cout << "No examples were provided exiting...\n" << std::endl;
        exit(-1);
    } 
    if(!load_test_cases()){
        std::cout << "Unable to parse test cases exiting...\n" << std::endl;
        exit(-1);
    }
}

Engine::~Engine(){
    clear_synth_state();
    for(auto m : this->examples){
        delete m;
    }
    delete this->target_synth_count;
    delete this->current_synth_count;
}

bool Engine::load_test_cases(){
    std::ifstream input(this->path_to_examples.c_str());
    std::ifstream infile();
    std::string line;
    for( std::string line; getline( input, line ); )
    {
        
        // std::cout << line << std::endl;

        size_t start;
        size_t end = 0;
        std::vector<std::string> out;
        while ((start = line.find_first_not_of(this->example_delimiter.c_str(), end)) != std::string::npos){
            end = line.find(this->example_delimiter.c_str(), start);
            out.push_back(line.substr(start, end - start));
        }
        
        update_examples(out);
        // std::string token = line.substr(0, s.find(delimiter)); // token is "scott"
    }
    // for(int i = 0 ; i < examples.size() ; i++){
    //     for(int j = 0 ; j < examples[i].size() ; j++){
    //         std::cout << std::get<0>(examples[i][j]) << " " << std::get<1>(examples[i][j]) << " " << std::get<2>(examples[i][j]) << " ";
    //     }
    //     std::cout << std::endl;
    // }
    return true;
}

void Engine::synth(){
    SynthState * ss = NULL;
    // keep track of how many we have synthesized before calling verify
    int count = 0;
    // for 1 to the maximum number of instructions
    // consruction permutations of function combinations and inputs
    // then verify they work for the input set of 
    for(int num_instr_to_choose = 1 ; num_instr_to_choose <= this->max_instrs ; num_instr_to_choose++){
        std::cout << "Synthesizing programs of size " << num_instr_to_choose << std::endl;
        choose_func(num_instr_to_choose);
        verify();

        if(count < *this->current_synth_count){
            count = *this->current_synth_count;
            std::cout << "Successfully Synthesized " << *this->current_synth_count << "/" << *this->target_synth_count << "\n" << std::endl;
        }
        if(*this->current_synth_count >= *this->target_synth_count)
            break;

        // if(ss){
        //     std::cout << "Successfully Synthesized " << *this->current_synth_count << "\n" << std::endl;
        //     this->dump_synthesized_function(ss);
        //     return;
        // }
        clear_synth_state();
    }
    this->dump_synthesized_function();
}

SynthState * Engine::verify(){
    std::cout<< "##VERIFYING##" << std::endl;
    std::map<std::vector<int>, SynthState *>::iterator it = this->synth_state.begin();
    it = this->synth_state.begin();
    for(it = this->synth_state.begin() ; it != synth_state.end() ; it++){
        for(int const_count = it->second->num_constants ; const_count < it->second->max_constants ; const_count++){
            it->second->synth_state_dump();
            std::cout << "Synthesizing with " << const_count << " constants for a maximum of " << it->second->max_constants << " constants" << std::endl;
            // for(int ele : it->first)
            //     std::cout << ele << " ";
            // std::cout << std::endl;

            // if(it->second->evaluate(&this->examples)){
            //     std::cout<< "##END VERIFYING##" << std::endl;
            //     return it->second;
            // }

            it->second->evaluate(&this->examples);

            // if there are any functions that were successfully synthesized add them
            if(it->second->successful_functions.size() > 0){
                for(auto f : it->second->successful_functions)
                    this->synthesized_functions.push_back(f);
            }
            // return if we have matched or exceeded our target synthesized function count
            if(*this->current_synth_count >= *this->target_synth_count){
                std::cout<< "##END VERIFYING##" << std::endl;
                return NULL;
            }
            it->second->update_constants(true);
        }
    }
    std::cout<< "##END VERIFYING##" << std::endl;
    return NULL;
}

void Engine::dump_exmaples(){
    std::cout << "##DUMPING EXAMPLES##" << std::endl;
    for(std::map<int, uint64_t> * m : this->examples){
        std::map<int, uint64_t>::iterator it;
        for (it = m->begin(); it != m->end(); it++) {
            std::cout << "\t" << it->first << ':' << it->second;
        }
        std::cout << std::endl;
    }
    std::cout << "##END DUMPING EXAMPLES##" << std::endl;
}


/*** PRIVATE ***/

void Engine::update_examples(std::vector<std::string> ex){
    // std::vector<std::tuple<int, int, uint64_t>> final_ex;
    std::map<int, uint64_t> * final_ex = new std::map<int, uint64_t>();

    // store the number of input arguments here
    int num_iargs = 0;

    // use a counter to represent the x-th input argument
    // use the x86 calling convention
    // call(1,2,3)
    // push 3 ; -3 off the stack
    // push 2 ; -2 off the stack
    // push 1 ; -1 off the stack
    int offset = -1;
    for(int i = 0 ; i < (int)ex.size() ; i += 3){
        int io, type;
        uint64_t val;
        // determine type
        if(ex[i] == this->out_delimiter.c_str())
            io = IO_OUT;
        else
            io = IO_IN;
        if(ex[i + 1] == this->int_delimiter.c_str()){
            type = TYPE_INT;
            val = (uint64_t)std::stoi(ex[i + 2].c_str());
        }
        // perform insert
        if(io == IO_IN){
            final_ex->insert({IO_IN + offset, val});
            offset--;
            num_iargs++;
        }
        // IO_OUT
        else{
            final_ex->insert({IO_OUT, val});
        }
        // std::tuple<int, int, uint64_t> tpl = std::make_tuple(io, type, val);
        // final_ex.push_back(tpl);
    }
    // initialized to negative so if this is negative assign
    if(this->num_input_arguments < 0){
        this->num_input_arguments = num_iargs;
    }
    // fail out when we detect an inconsistent number of input arguments
    else if(this->num_input_arguments != num_iargs){
        std::cout << "ENGINE: example number of input arguments is not consistent" << std::endl;
        exit(-1);
    }
    examples.push_back(final_ex);
}

void Engine::clear_synth_state(){
    std::map<std::vector<int>, SynthState *>::iterator it;
    for(it = this->synth_state.begin() ; it != this->synth_state.end(); it++){
        delete it->second;
    }
    this->synth_state.clear();
}

void Engine::choose_func(int num_func_to_choose){
    std::map<std::vector<int>, SynthState *>::iterator it = this->synth_state.begin();
    std::vector<std::vector<int>> ret;

    std::cout<< "FUNCS_NUM " << FUNCS_NUM << " NUM_FUNC_TO_CHOOSE " << num_func_to_choose << std::endl; 

    ret = nCk(FUNCS_NUM, num_func_to_choose);
    
    // for each combination
    for(std::vector<int> comb : ret){
        // print the combination
        std::cout << "FUNC COMBINATION: ";
        for(int ele : comb)
            std::cout << ele << " ";
        std::cout << std::endl;
        // generate the permutations of ordering
        do {
            std::cout << "\tPERMUTATION: ";
            for(int ele : comb)
                std::cout << ele << " ";
            std::cout << std::endl;
            // std::cout << "\t" << comb << '\n';
            
            // Add this instruction order to the synth_state map
            SynthState * ss = new SynthState(comb, this->num_input_arguments
                                        , this->target_synth_count, this->current_synth_count);
            this->synth_state.insert(it, std::pair<std::vector<int>, SynthState *>(comb, ss));
        } while(std::next_permutation(comb.begin(), comb.end()));
    }
    // it = this->synth_state.begin();
    // for(it = this->synth_state.begin() ; it != synth_state.end() ; it++){
    //     it->second->synth_state_dump();
    //     // for(int ele : it->first)
    //     //     std::cout << ele << " ";
    //     // std::cout << std::endl;
    // }
}

void Engine::dump_synthesized_function(){
    if(this->synthesized_functions.size() == 0){
        std::cout << "Unable to synthesize any functions for current parameters." << std::endl;
        return;
    }

    std::cout << "Able to synthesize the following functions." << std::endl << std::endl;

    for(auto f : this->synthesized_functions){
        std::cout << "#############" << std::endl;
        std::cout << f << std::endl;
        std::cout << "#############" << std::endl;
    }
}
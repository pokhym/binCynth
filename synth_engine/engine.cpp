#include <iostream>
#include <fstream>
#include <sstream>
#include "engine.hpp"
#include "components.hpp"


#ifndef DEBUG
#define DEBUG 1
#endif

Engine::Engine(std::string path_to_binary, std::string path_to_examples, int max_instrs, int num_input_arguments){
    std::cout <<"Initializing Engine stuff..." << std::endl;
    this->path_to_binary = path_to_binary;
    this->path_to_examples = path_to_examples;
    this->example_delimiter = ",";
    this->out_delimiter = "out";
    this->in_delimiter = "in";
    this->int_delimiter = "int";

    this->max_instrs = max_instrs;
    this->num_input_arguments = num_input_arguments;

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
    std::map<std::vector<int>, SynthState *>::iterator it;
    for(it = this->synth_state.begin() ; it != this->synth_state.end(); it++){
        delete it->second;
    }
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
    // declare a new SynthState
    // for(int max_num_instr = 1 ; max_num_instr <= this->max_instrs ; max_num_instr++){
        for(int num_instr_to_choose = 1 ; num_instr_to_choose <= this->max_instrs ; num_instr_to_choose++){
            int comp_id = choose_func(this->max_instrs, num_instr_to_choose);
        }
    // }
}

bool Engine::verify(){
    return true;
}

void Engine::update_examples(std::vector<std::string> ex){
    std::vector<std::tuple<int, int, uint64_t>> final_ex;

    for(int i = 0 ; i < (int)ex.size() ; i += 3){
        int io, type;
        uint64_t val;
        if(ex[i] == this->out_delimiter.c_str())
            io = IO_OUT;
        else
            io = IO_IN;
        if(ex[i + 1] == this->int_delimiter.c_str()){
            type = TYPE_INT;
            val = (uint64_t)std::stoi(ex[i + 2].c_str());
        }
        std::tuple<int, int, uint64_t> tpl = std::make_tuple(io, type, val);
        final_ex.push_back(tpl);
    }
    examples.push_back(final_ex);
}

int Engine::choose_func(int max_num_func, int num_func_to_choose){
    std::map<std::vector<int>, SynthState *>::iterator it = this->synth_state.begin();
    std::vector<std::vector<int>> ret;

    std::cout<< "MAX_NUM_FUNC " << max_num_func << " NUM_FUNC_TO_CHOOSE " << num_func_to_choose << std::endl; 

    ret = nCk(max_num_func, num_func_to_choose);
    
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
            SynthState * ss = new SynthState(comb, this->num_input_arguments);
            this->synth_state.insert(it, std::pair<std::vector<int>, SynthState *>(comb, ss));
        } while(std::next_permutation(comb.begin(), comb.end()));
    }
    it = this->synth_state.begin();
    for(it = this->synth_state.begin() ; it != synth_state.end() ; it++){
        it->second->synth_state_dump();
        // for(int ele : it->first)
        //     std::cout << ele << " ";
        // std::cout << std::endl;

    }
    return 0;
}

// std::vector<int> Engine::choose_arg_in(int id, int comp_id){
//     return NULL;
// }
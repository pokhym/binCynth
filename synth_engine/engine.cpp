#include <iostream>
#include <fstream>
#include <sstream>
#include "engine.hpp"
#include "components.hpp"


#ifndef DEBUG
#define DEBUG 1
#endif

Engine::Engine(std::string path_to_binary, std::string path_to_examples, int max_instrs){
    std::cout <<"Initializing Engine stuff..." << std::endl;
    this->path_to_binary = path_to_binary;
    this->path_to_examples = path_to_examples;
    this->example_delimiter = ",";
    this->out_delimiter = "out";
    this->in_delimiter = "in";
    this->int_delimiter = "int";

    this->max_instrs = max_instrs;

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
    for(int num_instr = 1 ; num_instr <= this->max_instrs ; num_instr++){
        int comp_id = choose_func(num_instr);
    }
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

int Engine::choose_func(int id){
    return 0;
}

// std::vector<int> Engine::choose_arg_in(int id, int comp_id){
//     return NULL;
// }
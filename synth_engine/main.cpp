#include <iostream>
#include "engine.hpp"

int main(int argc, char *argv[]){
    if(argc != 3){
        std::cout << "Usage:" << std::endl;
        std::cout << "\t./main <path_to_examples> <path_to_binary>" << std::endl;;
        return -1;
    }
    std::string path_to_binary, path_to_examples;
    path_to_examples = argv[1];
    path_to_binary = argv[2];
    // path_to_binary = "";
    // path_to_examples = "tests/example1.txt";
    Engine *a = new Engine(path_to_binary, path_to_examples, 3);
    std::cout << a->path_to_examples << std::endl;
    a->dump_exmaples();
    a->synth();
    delete a;
    return 0;
}
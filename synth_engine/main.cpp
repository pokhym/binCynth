#include <iostream>
#include "engine.hpp"

int main(int argc, char *argv[]){
    if(argc != 3){
        std::cout << argc << std::endl;
        std::cout << "Usage:" << std::endl;
        std::cout << "\t./main <path_to_examples> <partial_path_to_output_synthed>" << std::endl;;
        std::cout << "\t./main home/user/ex1.txt /home/user/synthed_" << std::endl;
        std::cout << "\t\t/home/user/synth_ will be transformed into /home/user/synthed_<N>.cpp by the engine" << std::endl;
        return -1;
    }
    std::string path_to_examples, partial_output_path;
    path_to_examples = argv[1];
    partial_output_path = argv[2];
    // path_to_binary = "";
    // path_to_examples = "tests/example1.txt";
    Engine *a = new Engine(path_to_examples, partial_output_path, 5);
    std::cout << a->path_to_examples << std::endl;
    a->dump_exmaples();
    int ret = a->synth();
    delete a;
    return ret;
}
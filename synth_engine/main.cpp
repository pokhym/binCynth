#include <iostream>
#include "engine.hpp"

int main(){
    std::string path_to_binary, path_to_examples;
    path_to_binary = "";
    path_to_examples = "tests/example1.txt";
    Engine *a = new Engine(path_to_binary, path_to_examples, 2, 2);
    std::cout << a->path_to_examples << std::endl;
    a->synth();
    delete a;
    return 0;
}
#include "component_state.hpp"

/*** PUBLIC ***/

ComponentState::ComponentState(){}

ComponentState::~ComponentState(){}

int ComponentState::create_constant_iarg(int offset){
    int const_id = -1 * FUNCS_MAX_IARGS - 1 - this->func_choice_id * 2 * pow(2, CONST_MAX_BIT) - offset;
    // int const_id = -1 * (this->func_choice_id + 1) * FUNCS_MAX_IARGS - this->func_choice_id * 2 * pow(2, CONST_MAX_BIT) - i - offset - 1;
    this->const_map.insert({const_id, -1 * pow(2, CONST_MAX_BIT) + offset});
    return const_id;
}

bool ComponentState::is_constant_iarg(int in_id){
    if(this->const_map.count(in_id) != 0)
        return true;
    else
        return false;
}
#include "components.hpp"

int int_add(int a, int b){
    return a + b;
}

int int_sub(int a, int b){
    return a - b;
}

int int_mul(int a, int b){
    return a * b;
}
int int_choose_gt(int a, int b){
	if(a > b)
        return a;
    else
        return b;
}
// int intp_mod(int * p, int idx, int val){
//     if(idx < STATIC_MEMORY_MAX_SIZE && idx >= 0){
//         p[idx] = val;
//         return 0;
//     }
//     else
//         return -1;
// }

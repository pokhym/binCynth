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
int intp_mod(int * p, int idx, int val){
    if(idx < STATIC_MEMORY_MAX_SIZE && idx >= 0){
        p[idx] = val;
        return 0;
    }
    else
        return -1;
}
int synthed_4(int in_1){
	int out_0 = int_add(1, in_1);
	return out_0;
}
int synthed_5(int in_1,int in_2){
	int out_0 = int_add(4, in_2);
	int out_1 = int_add(in_1, out_0);
	int out_2 = int_add(in_1, out_1);
	return out_2;
}

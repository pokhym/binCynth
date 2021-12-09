"""
    This file contains a simple script to generate integer inputs for our Triton execution
    We assume that a use always knows the interface to the top level function.

    For example if we have a function

    int main(int argc, char *argv[]){
        int a = (int)argv[0];
        int b = func1(a);
        b = func2(b)
        return b + 5;
    }

    we assume that the user knows that it should only provide 1 input argument.
    
    Triton will be able to collect the fact that we pass argument "a" to func1 and "b" to func2
    and the fact that "b + 5" will finally be returned
"""
import random


NUM_EXAMPLES = 100
NUM_INPUT_ARGUMENTS = 1
INT32_IDENTIFIER = "int32"
TYPE_SEP = ","
ARG_SEP = ","
INT_MIN = 0
INT_MAX = 100

"""
    An example will have the format of

        type,value1,type,value2,
        type,value3,type,value4,
    
    One example per line and the type at the front
"""

def create_int_only(idx : int, num_input : int):
    with open("triton_int_only_example_" + str(idx) + ".txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            for j in range(num_input):
                fd.write(INT32_IDENTIFIER + TYPE_SEP + str(random.randint(INT_MIN,INT_MAX)) + ARG_SEP)
            fd.write("\n")
            a = random.randint(INT_MIN, INT_MAX)
            for j in range(num_input):
                fd.write(INT32_IDENTIFIER + TYPE_SEP + str(a) + ARG_SEP)
            fd.write("\n")
        fd.close()

create_int_only(2, 2)

# i1 = 52
# i2 = 86
# o0 = 4 + i2
# o1 = i1 + o0
# o2 = o1 + i1
# print(o2)

# def modify_stuff2(a):
#     return a + 1
# def modify_stuff(a, b):
#     a = modify_stuff2(a)
#     return 2 * modify_stuff2(a) + b

# print(modify_stuff(i1,i2))
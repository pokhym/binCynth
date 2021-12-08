#ifndef COMPONENTS_H
#define COMPONENTS_H

/*** STATIC_MEMORY_MAX_SIZE ***/
// static const int STATIC_MEMORY_MAX_SIZE = 32;
/*** END STATIC_MEMORY_MAX_SIZE ***/

/*** STATIC_MEMORY ***/
// static int STATIC_MEMORY_1[STATIC_MEMORY_MAX_SIZE];
// static int STATIC_MEMORY_2[STATIC_MEMORY_MAX_SIZE];
/*** END STATIC_MEMORY_ARRAYS ***/

/*** CONST_MAX_BIT ***/
static const int CONST_MAX_BIT = 4;

/*** FUNC_PTR_TYPES ***/
typedef void (* func_ptr) (void);
// typedef int (* func_ptr_o_int_i_intp_i_int_i_int)(int *);
typedef int (* func_ptr_o_int_i_int)(int);
typedef int (* func_ptr_o_int_i_int_i_int)(int, int);
/*** FUNC_PTR_TYPES ***/

/*** FUNC_DEFINITION ***/
int int_add(int a, int b);
int int_sub(int a, int b);
int int_mul(int a, int b);
int int_choose_gt(int a, int b);
// int intp_mod(int * p, int idx, int val);
/*** END FUNC_DEFINITION ***/

/*** FUNCS_NUM ***/
static const int FUNCS_NUM = 4;
/*** END FUNCS_NUM ***/

/*** FUNC_PTR_TYPE_ENUM ***/
enum {
    e_func_ptr,
    // e_func_ptr_o_int_i_intp_i_int_i_int,
    e_func_ptr_o_int_i_int,
    e_func_ptr_o_int_i_int_i_int,
};

/*** END FUNC_PTR_TYPE_ENUM ***/

/*** FUNC_PTR_TYPE_CAST ***/
static const int FUNC_PTR_TYPE_CAST[FUNCS_NUM] = {
    e_func_ptr_o_int_i_int_i_int,
    e_func_ptr_o_int_i_int_i_int,
    e_func_ptr_o_int_i_int_i_int,
    e_func_ptr_o_int_i_int_i_int,
    // e_func_ptr_o_int_i_intp_i_int_i_int,
};
/*** END FUNC_PTR_TYPE_CAST ***/

/*** FUNC_NAMES ***/
static const char * FUNC_NAMES[FUNCS_NUM] = {
    "int_add",
    "int_sub",
    "int_mul",
    "int_choose_gt",
    // "intp_mod",
};
/*** END FUNC_NAMES ***/

/*** FUNC_CODE ***/
static const char * FUNC_CODE[FUNCS_NUM] = {
    "int int_add(int a, int b){\n\treturn a + b;\n}\n",
    "int int_sub(int a, int b){\n\treturn a - b;\n}\n",
    "int int_mul(int a, int b){\n\treturn a * b;\n}\n",
    "int int_choose_gt(int a, int b){\n\tif(a > b)\n\t\treturn a;\n\telse\n\t\treturn b;\n}\n",
    // "int intp_mod(int * p, int idx, int val){\n\tif(idx < STATIC_MEMORY_MAX_SIZE && idx >= 0){\n\t\tp[idx] = val;\n\t\treturn 0;\n\t}\n\telse\n\t\treturn -1;\n}\n"
};
/*** END FUNC_CODE ***/

/*** FUNCS_MAX_IARGS ***/
static int FUNCS_MAX_IARGS = 2;
/*** END FUNCS_MAX_IARGS ***/

/*** FUNCS_NUM_IARGS ***/
static int FUNCS_NUM_IARGS[FUNCS_NUM] {
    2,
    2,
    2,
    2,
    // 3,
};
/*** END FUNCS_NUM_IARGS ***/

/*** FUNCS_NUM_OARGS ***/
static int FUNCS_NUM_OARGS[FUNCS_NUM] {
    1,
    1,
    1,
    1,
    // 1,
};
/*** END FUNCS_NUM_OARGS ***/

/*** FUNCS ***/
const func_ptr FUNCS[FUNCS_NUM] {
    (func_ptr) int_add,
    (func_ptr) int_sub,
    (func_ptr) int_mul,
    (func_ptr) int_choose_gt,
    // (func_ptr) intp_mod,
};
/*** END FUNCS ***/


#endif // COMPONENTS_H
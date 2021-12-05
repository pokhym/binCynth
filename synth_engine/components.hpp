#ifndef COMPONENTS_H
#define COMPONENTS_H

/*** CONST_MAX_BIT ***/
static const int CONST_MAX_BIT = 5;

/*** FUNC_DEFINITION ***/
int int_add(int a, int b);
int int_sub(int a, int b);
int int_mul(int a, int b);
/*** END FUNC_DEFINITION ***/

/*** FUNCS_NUM ***/
static const int FUNCS_NUM = 3;
/*** END FUNCS_NUM ***/

/*** FUNC_NAMES ***/
static const char * FUNC_NAMES[FUNCS_NUM] = {
    "int_add",
    "int_sub",
    "int_mul",
};
/*** END FUNC_NAMES ***/

/*** FUNC_CODE ***/
static const char * FUNC_CODE[FUNCS_NUM] = {
    "int int_add(int a, int b){\n\treturn a + b;\n}\n",
    "int int_sub(int a, int b){\n\treturn a - b;\n}\n",
    "int int_mul(int a, int b){\n\treturn a * b;\n}\n",
};
/*** END FUNC_CODE ***/

/*** FUNCS_NUM_IARGS ***/
static int FUNCS_NUM_IARGS[FUNCS_NUM] {
    2,
    2,
    2,
};
/*** END FUNCS_NUM_IARGS ***/

/*** FUNCS_MAX_IARGS ***/
static int FUNCS_MAX_IARGS = 2;
/*** END FUNCS_MAX_IARGS ***/

/*** FUNCS_NUM_OARGS ***/
static int FUNCS_NUM_OARGS[FUNCS_NUM] {
    1,
    1,
    1,
};
/*** END FUNCS_NUM_OARGS ***/

/*** FUNCS ***/
static int (*FUNCS[FUNCS_NUM]) (int, int) {
    int_add,
    int_sub,
    int_mul,
};
/*** END FUNCS ***/


#endif // COMPONENTS_H
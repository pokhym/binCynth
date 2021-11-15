#ifndef COMPONENTS_H
#define COMPONENTS_H
int int_add(int a, int b);
int int_sub(int a, int b);
int int_mul(int a, int b);

static int FUNCS_NUM = 3;
static int FUNCS_NUM_IARGS[3] {2, 2, 2};
static int FUNCS_NUM_OARGS[3] {1, 1, 1};
static int (*FUNCS[3]) (int, int) {int_add, int_sub, int_mul};


#endif // COMPONENTS_H
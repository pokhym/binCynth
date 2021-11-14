#ifndef COMPONENTS_H
#define COMPONENTS_H
int int_add(int a, int b);
int int_sub(int a, int b);
int int_mul(int a, int b);

#ifndef FUNCSS
#define FUNCSS

static int (*FUNCS[3]) (int, int) {int_add, int_sub, int_mul};

#endif


#endif // COMPONENTS_H
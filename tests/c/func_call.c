int modify_stuff2(int a){
    return a + 1;
}
int modify_stuff(int a, int b){
    return 2 * modify_stuff2(a) + b;
}
int main(void){
    int a = 5;
    int b = 1;
    a++;
    return modify_stuff(a, b);
}
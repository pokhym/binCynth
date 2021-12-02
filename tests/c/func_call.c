int modify_stuff2(int a){
    return a + 1;
}
int modify_stuff(int a){
    return 2 * modify_stuff2(a);
}
int main(void){
    int a = 5;
    return modify_stuff(a);
}
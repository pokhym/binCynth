// ret = 2 * (a * a) + b
int f3(int a, int b){
    return 2 * a - b;
}
int f2(int a, int b){
    return a + f3(a, b);
}
int f1(int a, int b){
    a = a + 1;
    return a + f2(a, b);
}
int main(){
    int a;
    int b;
    return f1(a, b);
}
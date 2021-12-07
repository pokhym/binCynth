int f1(int a, int b){
    return 2 * a;
}
int f(int a, int b){
    int c = a + 5;
    return f1(c, a) - b;
}
int main(){
    int a;
    int b;
    return f(a, b);
}
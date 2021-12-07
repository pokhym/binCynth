int f1(int a, int b){
    return a + b + 0 - b + b;
}
int f(int a, int b){
    return f1(a, b) * 2 + b;
}
int main(){
    int a;
    int b;
    return f(a, b);
}
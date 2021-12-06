int f2(int a){
    return a % 5;
}
int f1(int a, int b){
    a = a + f2(a);
    return a + b * 2;
}
int main(){
    int a;
    int b;
    return f1(a, b);
}
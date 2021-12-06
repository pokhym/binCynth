// int f3(int a){
//     return a / 2;
// }
// int f2(int a, int b){
//     a = a + a;
//     return a * b;
// }
// int f1(int a, int b){
//     return f2(a, b) + f3(b);
// }

int f2(int a, int b){
    return a * b;
}
int f1(int a , int b){
    a = a + a;
    return f2(a, b) + b / 2;
}
int main(){
    int a;
    int b;
    return f1(a, b);
}
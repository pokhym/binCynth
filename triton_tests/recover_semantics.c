// % gcc -m32 recover_semantics.c -o recover_semantics
// % ndisasm -b 32 recover_semantics > recover_semantics.asm
int get_a(int a){
    return a * a;
}
int main() {
    int d = 0x1234;
    int a;
    return a * a;
}
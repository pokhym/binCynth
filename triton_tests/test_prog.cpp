int main(){
    asm (// "mov %1, %0\n\t"
    "add $0, %rax"
    // : "=r" () 
    // : "r" ()
    )
    ;
}
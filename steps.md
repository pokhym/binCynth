
1. obtain the function in binary form (fuzzing)
2. obtain the input/outputs of that binary function
3. synthesize an equivalent thing to part 2 in component based synthesis --> p
    permutation generation is complete (need double checking)

    out,int,12,in,int,2,in,int,4
    out,int,90,in,int,8,in,int,10

    c = mul(a,b), c = plus(a,b)
    a * b + -128 128

    ? = mul(?,?)

    ? = plus(?,?)

    ? = mul(?,?)
    ? = plus(?,?)

    ? = plus(?,?)
    ? = mul(?,?)

    c = mul(b,a)
    d = plus(a,c)
    return d

    c = mul(b,a)
    d = plus(a,b)
    return d

    c = mul(b,a)
    d = plus(c,c)
    return d



4. synthesize --> p'
    synthesis/verfication io examples (incomplete)
5. check p == p'
    python version compelte
    need to write C++ version of the check_equivalenc.py (incomplete)
6. check p == step 2
    python version complete
    need to write C++ version of the check_equivalenc.py (incomplete)
7. add to components
    not sure how to probably use bash script (incomplete)

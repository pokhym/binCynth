import random

NUM_EXAMPLES = 100

def example1():
    """
        in:
            int a
            int b
        out:
            ret = a * b + b
    """
    with open("../example1.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            b = random.randint(0, 10)
            c = a * b + b
            out = "out,int32," + str(c) + ",in,int32," + str(a) + ",in,int32," + str(b) +"\n"
            fd.write(out)
        fd.close()

def example2():
    """
        in:
            int a
        out:
            ret = a - 15
    """
    with open("../example2.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            ret = a - 15
            out = "out,int32," + str(ret) + ",in,int32," + str(a) + "\n" 
            fd.write(out)
        fd.close()

def example3():
    """
        in:
            int a
            int b
        out:
            ret = 2 * (a + 1) + b
    """
    with open("../example3.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            b = random.randint(0, 10)
            ret = 2 * (a + 1) + b
            out = "out,int32," + str(ret) + ",in,int32," + str(a) + ",in,int32," + str(b) + "\n" 
            fd.write(out)
        fd.close()

def example4():
    """
        in:
            int a
        out:
            ret = a - a + 1
    """
    with open("../example4.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            ret = a - a + 1
            out = "out,int32," + str(ret) + ",in,int32," + str(a) + "\n" 
            fd.write(out)
        fd.close()

def example5():
    """
        in:
            int a
        out:
            ret = a + 1
    """
    with open("../example5.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            ret = a + 1
            out = "out,int32," + str(ret) + ",in,int32," + str(a) + "\n" 
            fd.write(out)
        fd.close()

def example6():
    """
        in:
            int a
        out:
            ret = 2 * a + b
    """
    with open("../example6.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            b = random.randint(0, 10)
            ret = 2 * a + b - 3
            # ret = a + b
            out = "out,int32," + str(ret) + ",in,int32," + str(a) + ",in,int32," + str(b) + "\n" 
            fd.write(out)
        fd.close()

if __name__ == "__main__":
    print("Generating examples...")
    # example1()
    # example2()
    # example3()
    # example4()
    # example5()
    example6()
    print("Finished generating examples...")
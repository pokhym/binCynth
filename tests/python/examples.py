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
    with open("example1.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            b = random.randint(0, 10)
            c = a * b + b
            out = "out,int," + str(c) + ",in,int," + str(a) + ",in,int," + str(b) +"\n"
            fd.write(out)
        fd.close()

def example2():
    """
        in:
            int a
        out:
            ret = a - 15
    """
    with open("example2.txt", "w") as fd:
        for i in range(NUM_EXAMPLES):
            a = random.randint(0, 10)
            ret = a - 15
            out = "out,int," + str(ret) + ",in,int," + str(a) + "\n" 
            fd.write(out)
        fd.close()

if __name__ == "__main__":
    print("Generating examples...")
    example1()
    example2()
    print("Finished generating examples...")
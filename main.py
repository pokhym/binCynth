import sys
from os.path import abspath

sys.path.append("/usr/lib/python3.8/site-packages")
sys.path.append(abspath("gen_ex"))

import func_extraction

fe = func_extraction.FunctionExtractor("/home/user/pysynth/tests/python/triton_int_only_example_1.txt", "/home/user/pysynth/tests/c/func_call")
fe.run()
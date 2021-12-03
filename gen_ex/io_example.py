from typing import Dict, List, Tuple

MAIN_STACK_OFFSET = 8

class IOExample():
    i_args : List[List[Tuple[int, Tuple[int, int]]]] # (ebp offset, (size, val))
    o_args : List[List[Tuple[str, int]]] # (reg, val)

    def __init__(self):
        self.i_args = []
        self.o_args = []

    def add_iargs(self, i_args : Dict[Tuple[int, int], Tuple[int, int]]):
        """
            format is determined by FunctionInfo.i_args
        """
        i = []
        for k, v in i_args.items():
            i.append((k[1], v))
        i = sorted(i, key=lambda x: x[0], reverse=True)
        self.i_args.append(i)
    
    def add_func0_iargs(self, i_args : List[Tuple[int, int]]):
        """
            format determined by parse_examples() in func_extraction.py
            Currently List[Tuple[int, int]] = [(size, val)]
        """
        i = []
        for ia in i_args:
            i.append((-MAIN_STACK_OFFSET - ia[0], ia[1]))
        i = sorted(i, key=lambda x: x[0], reverse=True)
        self.i_args.append(i)
        
    def add_oargs(self, o_args : Dict[str, int]):
        """
            format is determined by FunctionInfo.o_args
            TODO: Sort?
        """
        o = []
        for k, v in o_args.items():
            o.append((k, v))
        self.o_args.append(o)
import sys
from os.path import abspath, exists, isfile, join
from os import listdir, chdir, getcwd, remove
import subprocess
import re
from typing import List
import glob
import logging
import time

from gen_ex.execution_info import OUTPUT_REGISTERS

sys.path.append("/usr/lib/python3.8/site-packages")
sys.path.append(abspath("gen_ex"))
sys.path.append(abspath("equivalence"))

import func_extraction
import equivalence_test

CURRENT_WORKING_DIRECTORY = getcwd()
SYNTH_ENGINE_FOLDER = "synth_engine"
SYNTH_ENGINE_EXECUTABLE_PATH = "synth_engine/main"
PARTIAL_OUTPUT_PATH = "synthed_"
PARITAL_OUTPUT_FOLDER_PATH = ""
PARTIAL_SYNTHED_CPP = "synthed_"
COMPONENTS_HPP_PATH = "synth_engine/components.hpp"
COMPONENTS_CPP_PATH = "synth_engine/components.cpp"
SMT_FILE_NAME = "out.smt2"

def modify_components_hpp(synthed_c_name : str, synthed_c : List[str]):
    """
        returns function code for the synthesized function
    """
    chpp = []
    with open(abspath(COMPONENTS_HPP_PATH), "r") as chpp_fd:
        while True:
            buf = chpp_fd.readline()
            if not buf:
                break
            chpp.append(buf)
        chpp_fd.close()

    # synthed function's number of inputs
    synthed_num_input = 0
    synthesized_func_only = ""

    new_funcs_num = None
    # calculate new function number
    for l_idx in range(0, len(chpp)):
        if "/*** END FUNCS_NUM ***/" in chpp[l_idx + 1]:
            m = re.search(r"[0-9]+", chpp[l_idx])
            new_funcs_num = int(m[0]) + 1
            break
    assert(new_funcs_num != None)

    # update FUNC_DEFINITION
    current_index = 0
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNC_DEFINITION ***/" in chpp[l_idx]:
            # find the beginning of the function
            for sc_idx in range(len(synthed_c)):
                if "{" in synthed_c[sc_idx] and synthed_c_name in synthed_c[sc_idx]:
                    synthed_c_name = re.sub(r"synthed_[0-9]+", "synthed_" + str(new_funcs_num), synthed_c_name, 1)
                    bracket_idx = synthed_c[sc_idx].rfind("{")
                    func_def = synthed_c[sc_idx][:bracket_idx] + ";\n"
                    func_def = re.sub(r"synthed_[0-9]+", "synthed_" + str(new_funcs_num), func_def, 1)
                    chpp.insert(l_idx, func_def)
                    term = True
                    current_index = l_idx
                    # find the number of input arguments
                    m = re.findall(r"\(.*\)", synthed_c[sc_idx])
                    assert(len(m)) == 1
                    synthed_num_input = m[0].count("in_")

                    # build the synthesized function
                    for sss in range(sc_idx, len(synthed_c)):
                        if "}\n" == synthed_c[sss]:
                            synthesized_func_only += synthed_c[sss]
                            break
                        synthesized_func_only += synthed_c[sss]
                    synthesized_func_only = synthesized_func_only.replace("\n", "\\n")
                    synthesized_func_only = synthesized_func_only.replace("\t", "\\t")
                    break

    # update FUNCS_NUM
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNCS_NUM ***/" in chpp[l_idx + 1]:
            m = re.search(r"[0-9]+", chpp[l_idx])
            new_funcs_num = int(m[0]) + 1
            chpp[l_idx] = "static const int FUNCS_NUM = " + str(new_funcs_num) + ";\n"
            term = True
            current_index = l_idx
            match_func_name = re.findall(r"synthed_[0-9]+", synthesized_func_only)
            assert(len(match_func_name) >= 1)
            synthesized_func_only = re.sub(r"synthed_[0-9]+", "synthed_" + str(new_funcs_num), synthesized_func_only, 1)
            # synthesized_func_only[0] = synthesized_func_only[0].replace(match_func_name[0], "synthed_" + str(new_funcs_num))
            # synthesized_func_only = "".join(synthesized_func_only)
            break

    # update FUNC_PTR_TYPE_CAST
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNC_PTR_TYPE_CAST ***/" in chpp[l_idx + 1]:
            if synthed_num_input == 1:
                chpp.insert(l_idx, "\te_func_ptr_o_int_i_int,\n")
            elif synthed_num_input == 2:
                chpp.insert(l_idx, "\te_func_ptr_o_int_i_int_i_int,\n")
            term = True
            current_index = l_idx
            break
        
    # update FUNC_NAMES
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNC_NAMES ***/" in chpp[l_idx + 1]:
            chpp.insert(l_idx, "\t\"" + synthed_c_name + "\",\n")
            term = True
            current_index = l_idx
            break

    # update FUNC_CODE
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNC_CODE ***/" in chpp[l_idx + 1]:
            chpp.insert(l_idx, "\t\"" + synthesized_func_only + "\",\n")
            term = True
            current_index = l_idx
            break
    
    # update FUNC_NUM_IARGS
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNCS_NUM_IARGS ***/" in chpp[l_idx + 1]:
            chpp.insert(l_idx, "\t" + str(synthed_num_input) + ",\n")
            term = True
            current_index = l_idx
            break
    
    # update FUNC_NUM_OARGS
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNCS_NUM_OARGS ***/" in chpp[l_idx + 1]:
            # TODO: Assuming 1 output arg only
            chpp.insert(l_idx, "\t" + str(1) + ",\n")
            term = True
            current_index = l_idx
            break
    
    # update FUNCS
    term = False
    for l_idx in range(current_index, len(chpp)):
        if term == True:
            break
        if "/*** END FUNCS ***/" in chpp[l_idx + 1]:
            chpp.insert(l_idx, "\t(func_ptr) " + synthed_c_name + ",\n")
            term = True
            current_index = l_idx
            break

    with open(abspath(COMPONENTS_HPP_PATH), "w") as fd:
        fd.write("".join(chpp))
        fd.close()

    synthesized_func_only = synthesized_func_only.replace("\\n", "\n")
    synthesized_func_only = synthesized_func_only.replace("\\t", "\t")
    
    return synthesized_func_only

def modify_components_cpp(synth_c : str):
    with open(abspath(COMPONENTS_CPP_PATH), "a") as fd:
        fd.write(synth_c)
        fd.close()

def get_function_length(synthed_c_name : str, synthed_c : List[str]):
    # synthed function's number of inputs
    synthed_num_input = 0
    synthesized_func_only = ""

    # update FUNC_DEFINITION
    current_index = 0
    term = False

    # length of function
    synthed_c_len  = 0
    # find the beginning of the function
    for sc_idx in range(len(synthed_c)):
        if "{" in synthed_c[sc_idx] and synthed_c_name in synthed_c[sc_idx]:
            bracket_idx = synthed_c[sc_idx].rfind("{")
            func_def = synthed_c[sc_idx][:bracket_idx] + ";\n"
            # find the number of input arguments
            m = re.findall(r"\(.*\)", synthed_c[sc_idx])
            assert(len(m)) == 1
            synthed_num_input = m[0].count("in_")

            # build the synthesized function
            for sss in range(sc_idx, len(synthed_c)):
                if "}\n" == synthed_c[sss]:
                    synthesized_func_only += synthed_c[sss]
                    break
                synthesized_func_only += synthed_c[sss]
                synthed_c_len += 1
            synthesized_func_only = synthesized_func_only.replace("\n", "\\n")
            synthesized_func_only = synthesized_func_only.replace("\t", "\\t")
            break
    return synthed_c_len
    
# with open("synthed_4.cpp", "r") as fd:
#     chpp = []
#     while True:
#         buf = fd.readline()
#         if not buf:
#             break
#         chpp.append(buf)
#     fd.close()
#     func = modify_components_hpp("synthed_4", chpp)
#     modify_components_cpp(func)

if __name__ == "__main__":
    logging.info("Enter path to input examples for black box target binary...")
    # /home/user/pysynth/tests/python/triton_int_only_example_1.txt
    bb_input_examples = input()
    bb_input_examples = abspath(bb_input_examples)
    assert(exists(bb_input_examples))
    logging.info("Enter path to black box target binary...")
    # /home/user/pysynth/tests/c/main_has_in_between
    bb_binary = input()
    bb_binary = abspath(bb_binary)
    assert(exists(bb_binary))

    # recompile synth_engine
    logging.info("Recompiling synthesis engine...")
    chdir(abspath(SYNTH_ENGINE_FOLDER))
    ret = subprocess.run(["make"], capture_output=True)
    if ret.returncode != 0:
        logging.info("Failed to compile synth_engine function")
        exit(-1)
    chdir(CURRENT_WORKING_DIRECTORY)

    assert(exists(abspath(SYNTH_ENGINE_EXECUTABLE_PATH)))
    assert(exists(abspath(COMPONENTS_HPP_PATH)))
    assert(exists(abspath(COMPONENTS_CPP_PATH)))

    # Call function extraction on main function input arguments and binary
    logging.info("Extracting functions from binary...")
    fe = func_extraction.FunctionExtractor(bb_input_examples, bb_binary, False)
    # execute binary and return the list of examples as file paths
    io_file_paths = fe.run()

    # for each example file run synth_engine
    for iofp in io_file_paths:
        # exec
        logging.info("Synthesizing for " + iofp + "...")
        ret = subprocess.run([SYNTH_ENGINE_EXECUTABLE_PATH, abspath(iofp), abspath(PARTIAL_OUTPUT_PATH)], capture_output=False)
        if ret.returncode != 0:
            logging.info("Failed to synthesize.")
            exit(-1)
        
        # obtain the synthesized cpp files
        synthed_c = [f for f in listdir(abspath(PARITAL_OUTPUT_FOLDER_PATH)) \
            if isfile(join(PARITAL_OUTPUT_FOLDER_PATH, f)) \
            and re.match(PARTIAL_SYNTHED_CPP, join(PARITAL_OUTPUT_FOLDER_PATH, f)) != None]

        # compile synthesized cpp files
        logging.info("Compiling syntehsized C files...")
        for sc in synthed_c:
            ret = subprocess.run(["gcc", sc, "-o", sc.replace(".cpp", "")], capture_output=True)
            if ret.returncode != 0:
                logging.info("Failed to compile synthesized function")
                logging.info(sc)
                logging.info(ret.stderr.decode())
                exit(-1)
        
        # equivalence check
        logging.info("Performing equivalence check of synthesized binaries...")
        executable_names : List[str] = []
        for sc in synthed_c:
            executable_names.append(join(CURRENT_WORKING_DIRECTORY, sc.replace(".cpp", "")))
        assert(len(executable_names) == 2)
        # Create SMT2 file for 
        equivalence_test.equivalence_check_run(executable_names[0], executable_names[1], join(CURRENT_WORKING_DIRECTORY, SMT_FILE_NAME))
        assert(exists(join(CURRENT_WORKING_DIRECTORY, SMT_FILE_NAME)))
        # check equivalence by calling z3
        ret = subprocess.run(["z3", "-smt2", join(CURRENT_WORKING_DIRECTORY, SMT_FILE_NAME)], capture_output=True)
        # unsat means that both executables are equivalent
        if "unsat" not in ret.stdout.decode():
            logging.info("Failed equivalence check of synthesized functions")
            exit(-1)
        


        # check the lengths of functions and choose the shiorter one
        logging.info("Choosing shorter synthesized program...")
        curr_min_length = 9999999999999999999
        min_length_sc_idx = None
        for sc_idx in range(len(synthed_c)):
            with open(abspath(synthed_c[sc_idx]), "r") as fd:
                synthed = []
                while True:
                    buf = fd.readline()
                    if not buf:
                        break
                    synthed.append(buf)
                fd.close()
            sc_idx_len = get_function_length(synthed_c[sc_idx].replace(".cpp", ""), synthed)
            if sc_idx_len < curr_min_length:
                curr_min_length = sc_idx_len
                min_length_sc_idx = sc_idx
        assert(min_length_sc_idx != None)


        # add to components.hpp and cpp
        logging.info("Updating components...")
        with open(abspath(synthed_c[min_length_sc_idx]), "r") as fd:
            synthed = []
            while True:
                buf = fd.readline()
                if not buf:
                    break
                synthed.append(buf)
            fd.close()
            func = modify_components_hpp(synthed_c[min_length_sc_idx].replace(".cpp", ""), synthed)
            modify_components_cpp(func)
        
        # recompile synth_engine
        logging.info("Recompiling synthesis engine...")
        chdir(abspath(SYNTH_ENGINE_FOLDER))
        ret = subprocess.run(["make"], capture_output=True)
        if ret.returncode != 0:
            logging.info("Failed to compile synth_engine")
            # logging.info(ret.stdout.decode())
            logging.info(ret.stderr.decode())
            exit(-1)
        chdir(CURRENT_WORKING_DIRECTORY)

        logging.info("Attempting to remove temporary files from previous run...")
        synthed_files = glob.glob("synthed_*")
        try:
            remove(abspath(iofp))
        except:
            logging.info("Could not remove", iofp)
        for fp in synthed_files:
            try:
                remove(abspath(fp))
            except:
                logging.info("Could not remove", fp)
        try:
            remove(abspath(join(CURRENT_WORKING_DIRECTORY, SMT_FILE_NAME)))
        except:
            logging.info("Count not remove", SMT_FILE_NAME)


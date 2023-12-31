#!/usr/bin/env python3

# see repo certicoqwasm-testing for a standalone version of this

import os
from tqdm import tqdm
import subprocess

CWD = os.path.abspath(os.path.dirname(__file__))

def replace_calls(path_in, path_out):
    path_in = os.path.join(CWD, path_in)
    path_out = os.path.join(CWD, path_out)
    print(f"replacing calls with tailcalls {path_in}...")
    content = open(path_in).read()

    lines = content.split("\n")
    pp_function_idx = None
    for line in lines[::-1]:
        if "pretty_print_constructor" in line:
            pp_function_idx = int(line.split("(func")[1].replace(")", ""))
            break

    if pp_function_idx is None:
        print("""Expected to find function exported as pretty_print_constructor.
             (Fn calls in it should not be replaced to tail calls.)""")
        exit(1)

    if os.path.exists(path_out):
        os.remove(path_out)
    open(path_out, "w").close()

    with open(path_out, "a") as f:
        current_func_idx = None

        for line in tqdm(lines):
            # remember idx of current function
            if "func (;" in line: #)
                current_func_idx = int(line.split("(func (;")[1].split(";)")[0]) #)

            if current_func_idx != pp_function_idx and line.strip()[:4] == "call":
                line = line.replace("call", "return_call")

            f.write(f"{line}\n")


if __name__ == '__main__':
    files = open("TESTS").read().strip().split("\n")

    for f in files:
        path_in = os.path.join(CWD, f"CertiCoq.Benchmarks.tests.{f}.wat")
        path_out = os.path.join(CWD, f"CertiCoq.Benchmarks.tests.{f}-tailcalls.wat")
        path_out_wasm = os.path.join(CWD, f"CertiCoq.Benchmarks.tests.{f}.wasm") # overwrite original wasm file
        if os.path.exists(path_out_wasm):
            os.remove(path_out_wasm)
        replace_calls(path_in, path_out)
        ret = subprocess.run(["wat2wasm", "--enable-tail-call", path_out, "-o", path_out_wasm]).returncode
        print(f"replacing calls with tailcalls {path_in} done {'failure' if ret else 'success'}.\n")

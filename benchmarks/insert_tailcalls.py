#!/usr/bin/env python3

# FUNCTIONALITY: replace all calls with tail calls in stream of .wat file
# USAGE:  cat input.wat | tqdm --bytes | ./insert_tailcalls_stream.py > input-tailcalls.wat

import sys


def replace_calls():
    pp_function_idx = 2
    current_func_idx = None

    for line in sys.stdin:
        # remember idx of current function
        if "func (;" in line:
            current_func_idx = int(line.split("(func (;")[1].split(";)")[0])

        if current_func_idx != pp_function_idx and line.strip()[:4] == "call":
            line = line.replace("call", "return_call")

        if "pretty_print_constructor" in line and f"func {pp_function_idx}" not in line:
            sys.stderr.write(
                f"Pretty print expected to be at index {pp_function_idx}.\n"
                + "Check the script insert_tailcalls.py"
            )
            exit(1)

        sys.stdout.write(line)


if __name__ == "__main__":
    replace_calls()

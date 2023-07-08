#!/usr/bin/env python3

import os

cwd = os.path.abspath(os.path.dirname(__file__))
contents = open(os.path.join(cwd, "LambdaANF_to_WASM_correct.v")).read()
print(f"Contains: {contents.count('admit')} admit and {contents.count('Admitted')} Admitted.")

#!/usr/bin/env python3

import os
import sys
import subprocess

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

files = open("TESTS").read().strip().split("\n")

ret_code = 0

for f in files:
    name = f"./CertiCoq.Benchmarks.tests.{f}.js"
    assert os.path.isfile(name), f"didn't find js file {name}, did you run <make compilewasm>?"

    r = subprocess.run(["nodejs", name])
    if r.returncode != 0:
        ret_code = r.returncode

sys.exit(ret_code)

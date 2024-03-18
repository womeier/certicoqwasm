#!/usr/bin/env python3

import os
import sys
import subprocess

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

files = open("TESTS").read().strip().split("\n")

ret_code = 0

for f in files:
    folder = os.path.join(CWD, f"./rust/{f}-extracted/")
    assert os.path.isdir(folder), f"didn't find folder {folder}."

    print(f"\nrunning: {f}")
    os.chdir(folder)
    r = subprocess.run(["cargo", "run"])

    if r.returncode != 0:
        ret_code = r.returncode

sys.exit(ret_code)

#!/usr/bin/env python3

import os
import subprocess

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

files = open("TESTS").read().strip().split("\n")


for f in files:
    name = f"./CertiCoq.Benchmarks.tests.{f}.js"
    assert os.path.isfile(name), f"didn't find js file {name}, did you run <make compilewasm>?"

    subprocess.run(["nodejs", name])

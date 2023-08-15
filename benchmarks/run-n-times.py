#!/usr/bin/env python3

import subprocess
import sys
from tqdm import tqdm

program =  sys.argv[1]
n = int(sys.argv[2])

results = []

for i in tqdm(range(n)):
    out = subprocess.check_output(["node", "--stack-size=5000000", f"./CertiCoq.Benchmarks.tests.{program}.js"])
    res = str(out).split("took")[1].split("ms.")[0]
    results.append(float(res))

avg_ms = sum(results) / len(results)
print(f"ran {program} {n} times: avg: {avg_ms} ms")

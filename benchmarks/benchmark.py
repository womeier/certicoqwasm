#!/usr/bin/env python3

import os
import click
import pkg_resources
import subprocess
import json
from tqdm import tqdm
import time
import pathlib

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

# NODE = "/usr/bin/node"
NODE = "node"
measurements = ["time_startup", "time_main", "time_pp", "bytes_used"]

programs = [
    "demo1",
    "demo2",
    "list_sum",
#    "vs_easy",
#    "vs_hard",
    "binom",
    "color",
    "sha_fast",
    "even_10000",
    "ack_3_9",
#    "sm_gauss_nat",
#    "sm_gauss_N",
]


def get_info(path):
    if path[-1] == "/":
        path = path[:-1]
    if path[0:2] == "./":
        path = path[2:]

    benchmarks_info = {
        "cps-feb-01-24": "CPS, inserted tailcalls, naive 0ary (CoqPL)",
        "cps-0aryfast-feb-13-24": "CPS, inserted tailcalls (no return instrs)",
        "non-cps-feb-07-24": "non-CPS, (tailcalls, no return instrs) naive 0ary",
        "non-cps-0aryfast-return-feb-26-24": "non-cps, with return instr, 0ary",
        "non-cps-ifs-unnested-mrch-22-24": "non-cps (same as feb-26-24, update MC), don't nest if statements",
        "non-cps-grow-mem-func-mrch-24-24": "non-cps (same as mrch-22-24), grow_mem in separate function",
        "non-cps-br_if-apr-12-24": "non-cps (same as mrch-24-24), br_if instead of if return",
    }
    try:
        info = benchmarks_info[path.replace("binaries/", "")]
    except KeyError:
        print("Running new binaries. Did you run MAKE INSTALL?\n")
        time.sleep(1)
        info = path

    return info


def get_engine_version(engine):
    if engine == "wasmtime":
        packages = {d.project_name: d.version for d in pkg_resources.working_set}
        version = packages.get("wasmtime", "wasmtime-py not installed")
        return f"wasmtime-py ({version})"
    elif engine == "wasmtime-compile":
        r = subprocess.run(["wasmtime", "--version"], capture_output=True)
        return r.stdout.decode("ascii").strip().replace("-cli ", "-compile (") + ")"
    elif engine == "node":
        r = subprocess.run([NODE, "--version"], capture_output=True)
        return f"Node.js ({r.stdout.decode('ascii').strip()})"
    else:
        print(f"Engine {engine} not found.")
        exit(1)


def program_opt_name(program, flag):
    if flag[0] == "-":
        if flag[1] == "-":
            return f"{program}-opt_{flag[2:]}"
        else:
            return f"{program}-opt_{flag[1:]}"
    else:
        return f"{program}-unexpected-{flag}"


def create_optimized_programs(folder, flag):
    print(f"Creating programs optimized with wasm-opt {flag} in {folder}.")
    for program in tqdm(programs):
        program_opt = program_opt_name(program, flag)
        path_orig = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program}.wasm")
        path_opt = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program_opt}.wasm")
        if not os.path.exists(path_opt):
            subprocess.run(
                [
                    "wasm-opt",
                    flag,
                    "--enable-tail-call",
                    "--enable-reference-types",
                    "--enable-gc",
                    "--enable-mutable-globals",
                    path_orig,
                    "--output",
                    path_opt,
                ]
            )


def wasmtime_compile_programs(folder, wasmopt_flag):
    print(f"Compiling wasm modules AOT with wasmtime in {folder}.")
    for program in tqdm(programs):
        if wasmopt_flag is not None:
            program = program_opt_name(program, wasmopt_flag)

        path = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program}.wasm")
        if not os.path.exists(path):
            print(f"wasmtime compile: didn't find input program {path}, skipping.")
            continue

        path_compiled = os.path.join(
            folder, f"CertiCoq.Benchmarks.tests.{program}.cwasm"
        )
        if not os.path.exists(path_compiled):
            subprocess.run(
                [
                    "wasmtime",
                    "compile",
                    "-W",
                    "tail-call=y",
                    path,
                    "--output",
                    path_compiled,
                ]
            )


def single_run_node(folder, program, verbose):
    r = subprocess.run(
        [
            NODE,
            "--experimental-wasm-return_call",
            "--experimental-wasm-typed_funcref",
            "--experimental-wasm-gc",
            "--no-wasm-bounds-checks",
            "./run-node.js",
            folder,
            program,
        ],
        capture_output=True,
    )

    wasm_path = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program}.wasm")
    if r.returncode != 0:
        print(f"Running {wasm_path} returned non-0 returncode, stderr: {r.stderr}")
        exit(1)

    if verbose:
        print("STDOUT: " + r.stdout.decode("ascii"))
        print("STDERR: " + r.stdout.decode("ascii"))

    res = "{" + r.stdout.decode("ascii").split("{{")[1].split("}}")[0] + "}"
    return json.loads(res)


def single_run_wasmtime(folder, program, verbose):
    r = subprocess.run(
        [
            "python3",
            "run-wasmtime.py",
            folder,
            program,
        ],
        capture_output=True,
    )

    wasm_path = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program}.wasm")
    if r.returncode != 0:
        print(f"Running {wasm_path} returned non-0 returncode, stderr: {r.stderr}")
        exit(1)

    if verbose:
        print("STDOUT: " + r.stdout.decode("ascii"))
        print("STDERR: " + r.stdout.decode("ascii"))

    res = "{" + r.stdout.decode("ascii").split("{{")[1].split("}}")[0] + "}"
    return json.loads(res)


def single_run_wasmtime_compiled(folder, program):
    wasm_path = os.path.join(folder, f"CertiCoq.Benchmarks.tests.{program}.cwasm")

    start_main = time.time()
    subprocess.run(
        ["wasmtime",
         "run",
         "--allow-precompiled",
         "-W",
         "tail-call=y",
         "--invoke",
         "main_function",
         wasm_path,
         ]
    )
    stop_main = time.time()
    time_main = round((stop_main - start_main) * 1000)
    return { "time_main": time_main, "time_startup": 0, "time_pp":0, "bytes_used": None }


def latex_table(tests, measure, results):
    rows = [[binary_version] + ["N/A" if result.get(t) is None else f"{result[t][measure]}" for t in tests] for (binary_version, result) in results.items()]

    latex_rows = [" & ".join(row) + "\\\\ \n" for row in rows]
    latex_string = (("\\begin{table}\n")
                    +("\\caption{placeholder caption}\n")
                    +("\\label{tbl:placeholder-label}\n")
                    +("\\centering\n")
                    +("\\begin{tabular}{|" + "|".join(["l"] + ["r" for t in tests]) + "|}\n")
                    +("\\hline\n")
                    +(" & " + " & ".join(tests) + " \\\\")
                    +("\\hline\n")
                    +(("\\hline\n").join(latex_rows))
                    +("\\hline\n")
                    +("\\end{tabular}\n")
                    +("\\end{table}\n")).replace("_", "\\_")

    print(latex_string)



def org_table(tests, measure, results):
    rows = [[binary_version] + ["N/A" if result.get(t) is None else f"{result[t][measure]}" for t in tests] for (binary_version, result) in results.items()]

    org_rows = ["| " + " | ".join(row) + " |\n" for row in rows]

    org_string = (("|---|---" + "".join(["|---" for t in tests]) + "|\n")
                  +("|   | " + " | ".join(tests) + " |\n")
                  +("|---|---" + "".join(["|---" for t in tests]) + "|\n")
                  +(("|---|---" + "".join(["|---" for t in tests]) + "|\n").join(org_rows))
                  +("|---|---" + "".join(["|---" for t in tests]) + "|\n"))

    print(org_string)

@click.command()
@click.option("--engine", type=str, help="Wasm engine", default="node")
@click.option("--runs", type=int, help="Number of runs", default=10)
@click.option("--memory-usage", is_flag=True, help="Print lin.mem. used", default=False)
@click.option("--binary-size", is_flag=True, help="Print binary size", default=False)
@click.option("--folder", type=str, help="Folder to Wasm binaries", multiple=True, required=True)
@click.option("--wasm-opt", type=str, help="Wasm-opt optimizations flag")
@click.option("--verbose", is_flag=True, help="Print debug information", default=False)
@click.option("--print-latex-table", is_flag=True, help="Print results as latex table", default=False)
@click.option("--print-org-table", is_flag=True, help="Print results as org mode table", default=False)
def measure(engine, runs, memory_usage, binary_size, folder, verbose, wasm_opt, print_latex_table, print_org_table):
    if engine not in ["wasmtime", "wasmtime-compile", "node"]:
        print("Expected wasmtime or node runtime.")
        exit(1)
    if runs <= 0:
        print("Expected at least one run.")
        exit(1)

    all_results = dict()

    for f in folder:
        f_name = pathlib.PurePath(f).name

        description = get_info(f.strip())
        if wasm_opt is not None:
            description = description + f" ({wasm_opt})"
        engine_version = get_engine_version(engine)
        print(f"Running {description}, avg. of {runs} runs with {engine_version}.")

        folder_results = dict()
        for program in programs:
            program_name_orig = program
            path = os.path.join(f, f"CertiCoq.Benchmarks.tests.{program}.wasm")

            if not os.path.exists(path):
                print(f"Didn't find {path}, skipping.")
                continue

            if wasm_opt is not None:
                program = program_opt_name(program, wasm_opt)
                path = f"{f}/CertiCoq.Benchmarks.tests.{program}.wasm"
                if not os.path.exists(path):
                    print(f"Didn't find optimized binary: {path}")
                    create_optimized_programs(f, wasm_opt)
                    print("Done. Please run again.")
                    exit()

            if engine == "wasmtime-compile":
                path = os.path.join(f, f"CertiCoq.Benchmarks.tests.{program}.cwasm")
                if not os.path.exists(path):
                    print(f"Didn't find compiled, optimized binary: {path}")
                    wasmtime_compile_programs(f, wasm_opt)
                    print("Done. Please run again.")
                    exit()

            values = []
            for run in range(runs):
                res = None
                if engine == "node":
                    res = single_run_node(f, program, verbose)

                elif engine == "wasmtime":
                    res = single_run_wasmtime(f, program, verbose)

                elif engine == "wasmtime-compile":
                    res = single_run_wasmtime_compiled(f, program)

                assert res is not None, "No value returned."
                values.append(res)

            result = dict()
            for meas in measurements:
                result[meas] = list()

            for val in values:
                for meas in measurements:
                    if meas == "bytes_used" and val[meas] is None:
                        result[meas].append(None)
                    else:
                        result[meas].append(int(val[meas]))

            time_startup = round(sum(result["time_startup"]) / len(result["time_startup"]))
            time_main = round(sum(result["time_main"]) / len(result["time_main"]))
            time_pp = round(sum(result["time_pp"]) / len(result["time_pp"]))

            memory_in_kb = (
                int(result["bytes_used"][0] / 1000)
                if (runs > 0 and result["bytes_used"][0] is not None)
                else "N/A"
            )
            binary_size_in_kb = int(os.stat(path).st_size / 1000)

            folder_results[program_name_orig] = {
                "time_startup": time_startup,
                "time_main": time_main,
                "time_pp": time_pp,
                "bytes_used": memory_in_kb,
                "binary_size_in_kb": binary_size_in_kb,
            }

            # count spaces instead of using \t
            max_program_len = max(map(len, programs))
            program_orig_len = (
                len(program.split("-opt_")[0]) if "-opt_" in program else len(program)
            )
            program_pp = (max_program_len - program_orig_len) * " " + program

            print(
                f"{program_pp} : "
                f"startup: {time_startup:>4}, main: {time_main:>3}, pp: {time_pp:>2}"
                f", sum: {time_startup+time_main+time_pp:>4}"
                + (f", memory used: {memory_in_kb} KB" if memory_usage else "")
                + (f", bin size: {binary_size_in_kb:>4} KB" if binary_size else "")
            )

        all_results[f_name] = folder_results

    if print_latex_table:
        print("\nPrinting LaTeX tables:\n")

        for meas in measurements:

            if not memory_usage and meas == "bytes_used":
                continue

            print(f"\nPrinting LaTeX table for {meas}:")
            latex_table(programs, meas, all_results)

        if binary_size:
            print("\nPrinting LaTeX table for binary size:")
            latex_table(programs, "binary_size_in_kb", all_results)

    if print_org_table:
        print("\nPrinting org tables:\n")

        for meas in measurements:
            if not memory_usage and meas == "bytes_used":
                continue

            print(f"\nPrinting org table for {meas}:")
            org_table(programs, meas, all_results)

        if binary_size:
            print("\nPrinting org table for binary size:")
            org_table(programs, "binary_size_in_kb", all_results)

    print("")


if __name__ == "__main__":
    measure()

#!/usr/bin/env python3

import os
import click
import time
import subprocess
import pathlib

CWD = os.path.abspath(os.path.dirname(__file__))
os.chdir(CWD)

measurements = ["time_startup", "time_main", "time_pp"]

programs = [
    "demo1",
    "demo2",
    "list_sum",
    "binom",
    "sha_fast",
    "color",
    "sm_gauss_N",
    "sm_gauss_nat",
    "even_10000",
    "ack_3_9",
#    "bernstein_yang",
]


def single_compile_rust(folder, program):
    folder_path = os.path.join(os.path.join(CWD, folder), f"{program}-extracted")
    os.chdir(folder_path)

    r = subprocess.run(
        ["cargo", "build", "--release"],
        capture_output=False,
    )

    assert r.returncode == 0, f"Running {program} returned non-0 returncode"


def single_run_rust(folder, program, verbose):
    folder_path = os.path.join(
        os.path.join(CWD, folder), f"{program}-extracted/target/release"
    )
    os.chdir(folder_path)

    start_time = time.time()
    r = subprocess.run(
        [
            f"./{program}",
        ],
        capture_output=True,
    )
    end_time = time.time()

    assert r.returncode == 0, f"Running {program} returned non-0 returncode"

    if verbose:
        print("STDOUT: " + r.stdout.decode("ascii"))
        print("STDERR: " + r.stdout.decode("ascii"))

    time_startup = round((end_time - start_time) * 1000)
    return time_startup


def org_table(tests, measure, results):
    rows = [
        [binary_version]
        + ["N/A" if result.get(t) is None else f"{result[t][measure]}" for t in tests]
        for (binary_version, result) in results.items()
    ]

    org_rows = ["| " + " | ".join(row) + " |\n" for row in rows]

    org_string = (
        ("|---|---" + "".join(["|---" for t in tests]) + "|\n")
        + ("|   | " + " | ".join(tests) + " |\n")
        + ("|---|---" + "".join(["|---" for t in tests]) + "|\n")
        + (("|---|---" + "".join(["|---" for t in tests]) + "|\n").join(org_rows))
        + ("|---|---" + "".join(["|---" for t in tests]) + "|\n")
    )

    print(org_string)


@click.command()
@click.option("--runs", type=int, help="Number of runs", default=10)
@click.option("--binary-size", is_flag=True, help="Print binary size", default=False)
@click.option("--folder", type=str, help="Folder to Wasm binaries", required=True)
@click.option("--verbose", is_flag=True, help="Print debug information", default=False)
@click.option(
    "--print-org-table",
    is_flag=True,
    help="Print results as org mode table",
    default=False,
)
def measure(runs, binary_size, folder, verbose, print_org_table):
    assert runs > 0, "Expected at least one run."

    f_name = pathlib.PurePath(folder).name

    print("Compiling all programs...")
    for program in programs:
        single_compile_rust(folder, program)

    print(f"Running {f_name}, avg. of {runs} runs, rust binaries.")
    for program in programs:
        values = []
        for run in range(runs):
            res = single_run_rust(folder, program, verbose)

            assert res is not None, "No value returned."
            values.append(res)

        result = dict()
        for meas in measurements:
            result[meas] = list()

        for val in values:
            for meas in measurements:
                if meas not in ["time_startup", "time_main"]:
                    result["time_main"].append(int(val))

        time_main = round(sum(result["time_main"]) / len(result["time_main"]))

        # count spaces instead of using \t
        max_program_len = max(map(len, programs))
        program_pp = (max_program_len - len(program)) * " " + program

        #         print(
        #             f"{program_pp} : "
        #             f"startup: {time_startup:>2}, main: {time_main:>3}, pp: {time_pp:>2}"
        #             f", sum: {time_startup+time_main+time_pp:>4}"
        #         )

        print(f"{program_pp} : total: {time_main:>3}")


if __name__ == "__main__":
    measure()

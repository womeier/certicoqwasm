#!/usr/bin/python

from itertools import zip_longest
import sys
import subprocess
import pathlib
import re

finname = sys.argv[1]

def grouper(iterable, n, fillvalue=None):
    args = [iter(iterable)] * n
    return zip_longest(*args, fillvalue=fillvalue)

foutname = "compute.v"

p = pathlib.Path(foutname)

if p.exists():
    p.unlink()

i = 0

arith_pattern = re.compile(r"^\d+ (\+|\-|\*|\/|mod|>>|<<|land|lor|lxor) \d+")
carry_pattern = re.compile(r"^\d+ (\+|\-)c \d+")
carryc_pattern = re.compile(r"^(add|sub)carryc \d+ \d+")
compare_pattern = re.compile(r"^compare \d+ \d+")
boolops_pattern = re.compile(r"^\d+ (<|<=|=)\? \d+")
addmuldiv_pattern = re.compile(r"^addmuldiv \d+ \d+ \d+")
zerobitsops_pattern = re.compile(r"^(head|tail)0 \d+")
prodops_pattern = re.compile(r"(diveucl|diveucl_21|mulc) \d+ \d+")

def expr_name(s):
    m = arith_pattern.search(s)
    if m:
        match m.group(1):
           case "+":
               return "add"
           case "-":
               return "sub"
           case "*":
               return "mul"
           case "/":
               return "div"
           case "mod":
               return "mod"
           case "<<":
               return "lsl"
           case ">>":
               return "lsr"
           case "land":
               return "land"
           case "lor":
               return "lor"
           case "lxor":
               return "lxor"
    m = carry_pattern.search(s)
    if m:
        match m.group(1):
           case "+":
               return "addc"
           case "-":
               return "subc"
    m = carryc_pattern.search(s)
    if m:
        match m.group(1):
           case "add":
               return "addcarryc"
           case "sub":
               return "subcarryc"
    m = compare_pattern.search(s)
    if m:
        return "compare"
    m = boolops_pattern.search(s)
    if m:
        match m.group(1):
           case "=":
               return "eqb"
           case "<":
               return "ltb"
           case "<=":
               return "leb"
    m = addmuldiv_pattern.search(s)
    if m:
        return "addmuldiv"
    m = zerobitsops_pattern.search(s)
    if m:
        match m.group(1):
           case "head":
               return "head0"
           case "tail":
               return "tail0"
    m = prodops_pattern.search(s)
    if m:
        match m.group(1):
           case "diveucl":
               return "diveucl"
           case "diveucl_21":
               return "diveucl21"
           case "mulc":
               return "mulc"
    raise Exception(s)

with open(foutname, "w") as fout:
    fout.write('Set Warnings "-primitive-turned-into-axiom".\n')
    fout.write("Require Import String Uint63.\n")
    fout.write("Set Implicit Arguments.\n")
    fout.write("Open Scope uint63_scope.\n")
    fout.write("From CertiCoq.Plugin Require Import CertiCoq.\n")
    with open(finname, "r") as fin:
        lines = fin.read().splitlines()
        for line in lines:
            strs = line.split(" = ")
            if len(strs) > 1:
                defname = expr_name(strs[0]) + "_" + str(i)
                fout.write("Definition " + defname + " := " + strs[0] + ".\n")
                fout.write('Eval cbn in "' + defname + '"%string.\n')
                fout.write('Eval cbn in "' + strs[0] + '"%string.\n')
                fout.write("Eval cbn in " + defname + ".\n")
                fout.write("CertiCoq Compile Wasm " + defname + ".\n")
                i += 1

coqoutput = subprocess.run(['coqc', foutname], stdout=subprocess.PIPE).stdout.decode('utf-8')

string_pattern = re.compile(r'"(.+)"\%string')
res_pattern = re.compile(r'= (.+)$')

lines = coqoutput.split("\n")
l = len(lines)

i = 0

while i + 2 < l:
    line = lines[i]
    nm = string_pattern.search(line)
    if nm:
        dm = string_pattern.search(lines[i+2])
        rm = res_pattern.search(lines[i+4])
        wasmoutput = subprocess.run(['node', "./js/run_wasm.js", ".", nm.group(1)], stdout=subprocess.PIPE).stdout.decode('utf-8').strip("\n").strip()
        
        if wasmoutput != rm.group(1):
            print("Unexpected Wasm output for expression " + dm.group(1) + ":")
            print("Coq output: " + rm.group(1))
            print("Wasm output: " + wasmoutput)
        i += 5
        continue
    i += 1

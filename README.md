This repo contains a WebAssembly-backend for CertiCoq ([CPP'25](https://popl25.sigplan.org/details/CPP-2025-papers/9/CertiCoq-Wasm-A-verified-WebAssembly-backend-for-CertiCoq))
targeting the AST of the [WasmCert](https://github.com/WasmCert/WasmCert-Coq) mechanisation. (It is not yet available in upstream CertiCoq.)
Backend and correctness proof are in `theories/CodegenWasm/`,
there are no substantial changes to the rest, essentially only adjustments for testing and CI. <br>

### Basic setup (Linux/Mac)
Install [Node.js](https://nodejs.org/en/download/package-manager) (version 22 or higher), then:
```
opam switch create certicoqwasm ocaml.4.14.2

opam repo add coq-released https://coq.inria.fr/opam/released
git clone https://github.com/womeier/certicoqwasm && cd certicoqwasm

# just use CertiCoq-Wasm
opam install .

# setup for development
opam install . --deps-only
make && make install

# run benchmarks (prints S-expressions to stdout)
cd benchmarks/wasm && make
```
See [here](https://github.com/womeier/certicoqwasm-testing) for how to use, and performance evaluation.



original README:
----------------------------------

# CertiCoq

<p align="center">
<img src="https://certicoq.org/certicoq.png" alt="CertiCoqCoq" width="100px"/>
</p>

## Overview

[![build](https://github.com/CertiCoq/certicoq/actions/workflows/build.yml/badge.svg)](https://github.com/CertiCoq/certicoq/actions/workflows/build.yml)

![GitHub](https://img.shields.io/github/license/CertiCoq/certicoq)


CertiCoq is a compiler for Gallina, the specification language of the [Coq proof assistant](https://coq.inria.fr/refman/index.html). CertiCoq targets Clight, a subset of the C language that can be compiled with any C compiler, including the [CompCert](http://compcert.org) verified compiler.

Large parts of the CertiCoq compiler have been verified whereas others are in the process of being verified.

## Documentation

The [CertiCoq Wiki](https://github.com/PrincetonUniversity/certicoq/wiki) has instructions for using the [CertiCoq plugin](https://github.com/PrincetonUniversity/certicoq/wiki/The-CertiCoq-plugin) to compile Gallina to C and interfacing with the generated C code.

You can also find some demos [here](https://github.com/PrincetonUniversity/certicoq/blob/master/benchmarks/tests.v) and [here](https://github.com/PrincetonUniversity/certicoq/blob/master/benchmarks/axioms/tests.v).

## Installation Instructions

See [INSTALL.md](INSTALL.md)  for installation instructions.

## Current Members

Andrew Appel, Yannick Forster, Joomy Korkut, Zoe Paraskevopoulou, and Matthieu Sozeau.

## Past Members and Contributors

Abhishek Anand, Anvay Grover, John Li, Greg Morrisett, Randy Pollack, Olivier Savary Belanger, Matthew Weaver

## License 

CertiCoq is open source and distributed under the [MIT license](LICENSE.md).

## Directory structure

* `theories/` contains the sources of the compiler
* `plugin/` contains the CertiCoq plugin for Coq 
* `benchmarks/` contains the benchmark suite
* `glue/` contains the glue code generator
* `bootstrap/` contains the bootstrapped CertiCoq plugin for Coq and
  a CertiCoq-compiled variant of MetaCoq's safe type checker.

Structure of the theories directory:

* `theories/common`: contains common code utilities 
* `theories/Compiler`: contains the toplevel CertiCoq pipeline 
* `theories/LambdaBoxMut`: mutual inductive version of MetaCoq's LambdaBox erased language
* `theories/LambdaBoxLocal`: variant where deBruijn indices are represented using `N` instead of `nat`.
   The transformation from LambdaBoxMut let-binds the definitions in the environment to
   produce a closed term.
* `theories/LambdaANF` contains the λANF pipeline (and conversions -- direct and LambdaANF -- to λANF)
* `theories/Codegen` contains the C code generator.
* `theories/CodegenWasm` contains the Wasm code generator.


## Bugs 

We use github's [issue tracker](https://github.com/PrincetonUniversity/certicoq/issues) to keep track of bugs and feature requests.

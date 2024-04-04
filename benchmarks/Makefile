COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WATFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wat, $(TESTS))
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))
WASM2WAT=wasm2wat --enable-tail-call

#all: lib tests optimize runwasm
all: lib tests runwasm

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WASMFILES): tests

#optimize: $(WASMFILES)
#	wasm-opt -O2 --enable-tail-call --enable-mutable-globals $< --output tmp
#	mv tmp $<

runwasm:
	ulimit -s unlimited && ./run_wasm_benchmarks.py

clean:
	rm -f ./*.wat ./*.wasm ./*.tests.*.js *.ir
	rm -f ./*.vo
	rm -f ./*.vos
	rm -f ./*.vok
	rm -f ./*.glob

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

cleanlib:
	$(MAKE) clean -C lib

tests: tests.v
	ulimit -s unlimited && coqc $(COQOPTS) tests.v

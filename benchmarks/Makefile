COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WATFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wat, $(TESTS))
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))
JSFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.js, $(TESTS))
WAT2WASM=wat2wasm

all: lib tests runwasm

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WATFILES): tests

%.js: %.wasm
	cp ./run-wasm-template.js $@
	sed -i 's/{{file}}/$</g' $@

%.wasm: %.wat
	$(WAT2WASM) $<

compilewasm: $(WASMFILES)

runwasm: compilewasm $(JSFILES)
	./run_wasm_benchmarks.py

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
	ulimit -s unlimited
	coqc $(COQOPTS) tests.v


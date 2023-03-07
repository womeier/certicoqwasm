COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WATFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wat, $(TESTS))
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))
WAT2WASM=wat2wasm

all: lib tests compilewasm

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WATFILES): tests

%.wasm: %.wat
	$(WAT2WASM) $<

compilewasm: $(WASMFILES)

clean:
	rm -f ./*.c
	rm -f ./*.h
	rm -f ./*.wat ./*.wasm
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
	coqc $(COQOPTS) tests.v


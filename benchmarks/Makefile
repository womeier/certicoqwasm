COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WATFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wat, $(TESTS))
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))
JSFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.js, $(TESTS))
WASM2WAT=wasm2wat --enable-tail-call

OS=$(shell uname)

STACKSIZE=$(if $(filter Linux,$(OS)),unlimited,65532)

SED=$(if $(filter Linux,$(OS)),sed,gsed)

all: lib tests runwasm

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WASMFILES): tests

runwasm: $(WASMFILES)
	ulimit -s $(STACKSIZE) && ./run_wasm_benchmarks.py

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
	ulimit -s $(STACKSIZE) && coqc $(COQOPTS) tests.v

primitive_unit_tests:
	@coqc -quiet -R ./ CertiCoq.Benchmarks uint63_unit_tests.v
	@ulimit -s unlimited
	@node --stack-size=100000 js/run_uint63_unit_tests.js

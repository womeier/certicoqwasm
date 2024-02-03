COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WATFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wat, $(TESTS))
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))
JSFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.js, $(TESTS))
WASM2WAT=wasm2wat --enable-tail-call

#all: lib tests convert2wat tailcallify optimize runwasm
all: lib tests runwasm

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WASMFILES): tests

%.js: %.wasm
	cp ./run-wasm-template.js $@
	sed -i 's/{{file}}/$</g' $@

#%.wat: %.wasm
#	$(WASM2WAT) $< > $@

#convert2wat: $(WATFILES)

# currently: certicoqwasm generates normal calls -> replace them with tailcalls until this is added to wasmcert-coq
#tailcallify: $(WATFILES) convert2wat
#	./insert_tailcalls.py

#optimize: $(WASMFILES)
#	wasm-opt -O2 --enable-tail-call --enable-mutable-globals $< --output tmp
#	mv tmp $<

runwasm: $(JSFILES)
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

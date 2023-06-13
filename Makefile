.PHONY: all submodules plugin cplugin install clean bootstrap


all theories/Extraction/extraction.vo: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries -j`nproc`
	$(MAKE) -C theories -j`nproc`

theories/Makefile: theories/_CoqProject
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile: libraries/_CoqProject
	cd libraries;coq_makefile -f _CoqProject -o Makefile


submodules:
	./make_submodules.sh noclean

plugins: plugin cplugin

plugin: all plugin/CertiCoq.vo

plugin/Makefile: plugin/_CoqProject
	cd plugin ; coq_makefile -f _CoqProject -o Makefile

plugin/CertiCoq.vo: all plugin/Makefile theories/Extraction/extraction.vo
	bash ./make_plugin.sh plugin


cplugin: all cplugin/CertiCoq.vo

cplugin/Makefile: cplugin/_CoqProject
	cd cplugin ; coq_makefile -f _CoqProject -o Makefile

cplugin/CertiCoq.vo: all cplugin/Makefile theories/ExtractionVanilla/extraction.vo
	bash ./make_plugin.sh cplugin

bootstrap: plugin cplugin
	$(MAKE) -C bootstrap all

COQPROJECT_Q_ARGS := $(shell grep '^-R' theories/_CoqProject | grep --invert Extraction | grep --invert Runtime | grep --invert Glue)
ALECTRYON_CACHE := .alectryon.cache
ALECTRYON_FLAGS := --backend webpage $(COQPROJECT_Q_ARGS) \
	--long-line-threshold 80 \
	--cache-directory $(ALECTRYON_CACHE) --cache-compression

docs: docs/compilation.html docs/proof.html
	echo "<html> <body> <h1> Alectryon files for CertiCoq Wasm backend </h1> - <a href='compilation.html'> Compilation </a> <br> <br> - <a href='proof.html'> Correctness proof </a> (This file is big) </body </html>" > docs/index.html

docs/compilation.html: theories/CodegenWASM/LambdaANF_to_WASM.v
	cd theories && alectryon $(ALECTRYON_FLAGS) --frontend coq CodegenWASM/LambdaANF_to_WASM.v -o ../docs/compilation.html

docs/proof.html: theories/CodegenWASM/LambdaANF_to_WASM_correct.v
	cd theories && alectryon $(ALECTRYON_FLAGS) --frontend coq CodegenWASM/LambdaANF_to_WASM_correct.v -o ../docs/proof.html

install: plugin cplugin bootstrap
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C plugin install
	$(MAKE) -C cplugin install
	$(MAKE) -C bootstrap install

clean:
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
	$(MAKE) -C plugin clean
	$(MAKE) -C cplugin clean
	rm -f `find theories -name "*.ml*"`
	rm -rf plugin/extraction
	rm -rf docs/

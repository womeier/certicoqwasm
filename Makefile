.PHONY: all submodules runtime plugin cplugin install clean bootstrap


OS=$(shell uname)

CORES=$(if $(filter Linux,$(OS)),$(shell nproc),$(shell sysctl -n hw.logicalcpu))

all theories/Extraction/extraction.vo: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries -j $(CORES)
	$(MAKE) -C theories -j $(CORES)

theories/Makefile: theories/_CoqProject
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile: libraries/_CoqProject
	cd libraries;coq_makefile -f _CoqProject -o Makefile

submodules:
	./make_submodules.sh noclean

plugins: plugin cplugin

plugin: all runtime plugin/CertiCoq.vo

plugin/Makefile: plugin/_CoqProject
	cd plugin ; coq_makefile -f _CoqProject -o Makefile

plugin/CertiCoq.vo: all plugin/Makefile theories/Extraction/extraction.vo
	bash ./make_plugin.sh plugin


cplugin: all runtime cplugin/CertiCoq.vo

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
	echo "<html> <body> <h1> Alectryon files for CertiCoq Wasm backend (`git rev-parse --short HEAD`, `date +'%d %B %Y'`)</h1> - \
		<a href='compilation.html'> Compilation </a> <br> <br> - <a href='proof.html'> Correctness proof </a> (This file is big) </body </html>" > docs/index.html

docs/compilation.html: theories/CodegenWasm/LambdaANF_to_Wasm.v
	cd theories && alectryon $(ALECTRYON_FLAGS) --frontend coq CodegenWasm/LambdaANF_to_Wasm.v -o ../docs/compilation.html

docs/proof.html: theories/CodegenWasm/LambdaANF_to_Wasm_correct.v
	cd theories && alectryon $(ALECTRYON_FLAGS) --frontend coq CodegenWasm/LambdaANF_to_Wasm_correct.v -o ../docs/proof.html

#install: plugin cplugin bootstrap
install: plugin
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C runtime install
	$(MAKE) -C plugin install
#	$(MAKE) -C cplugin install
#	$(MAKE) -C bootstrap install

# Clean generated makefiles
mrproper: theories/Makefile libraries/Makefile plugin/Makefile cplugin/Makefile
	rm -f theories/Makefile
	rm -f libraries/Makefile
	rm -f plugin/Makefile
	rm -f cplugin/Makefile

clean: theories/Makefile libraries/Makefile plugin/Makefile cplugin/Makefile
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
	$(MAKE) -C runtime clean
	$(MAKE) -C plugin clean
	$(MAKE) -C cplugin clean
	$(MAKE) -C bootstrap clean
	rm -f `find theories -name "*.ml*"`
	rm -rf plugin/extraction
	rm -rf docs/
	rm -rf cplugin/extraction
	$(MAKE) mrproper

runtime: runtime/Makefile
	$(MAKE) -C runtime

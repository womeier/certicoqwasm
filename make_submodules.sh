#!/usr/bin/env bash

DOCLEAN=$1

clean() {
    if [ "$DOCLEAN" = "noclean" ]; then
        echo "Warning: not cleaning"
    else
        git clean -dfx
    fi
}

cd submodules

# cd metacoq
# echo "Rebuilding MetaCoq"
# clean
# ./configure.sh local
# make -j 2 translations all
# make install
# cd ..

cd coq-paco
echo "Building coq-paco"
clean
cd src
make
make -f Makefile.coq install
cd ../..

cd strong-induction
echo "Building Strong-Induction"
make
make install
cd ..

cd parseque
echo "Building parseque"
clean
make
make install
cd ..

cd interactiontrees
echo "Building interactiontrees"
clean
make
make install
cd ..

cd wasmcert
echo "Building wasmcert"
clean
make
make install
cd ..

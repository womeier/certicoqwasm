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

cd metacoq
echo "Rebuilding MetaCoq"
clean
./configure.sh local
make -j 2 translations all
make install
cd ..

cd parseque
echo "Rebuilding parseque"
clean
make
make install
cd ..

cd interactiontrees
echo "Rebuilding interactiontrees"
clean
make
make install
cd ..

cd wasmcert
echo "Rebuilding wasmcert"
clean
make
make install
cd ..

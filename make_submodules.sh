#!/usr/bin/env bash
set -e

DOCLEAN=$1

clean() {
    if [ "$DOCLEAN" = "noclean" ]; then
        echo "Warning: not cleaning"
    else
        git clean -dfx
    fi
}

cd submodules
cd ..

pwd -P
ls -l
ls -l submodules
cd submodules

# cd metacoq
# echo "Rebuilding MetaCoq"
# clean
# ./configure.sh local
# make -j 2 translations all
# make install
# cd ..

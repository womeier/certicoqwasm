#!/bin/bash

RUST_PATH=./rust/
RUST_SUFFIX_PATH=extracted/src/
RUST_SUFFIX=extracted/src/main.rs

rust_examples="demo1 demo2 list_sum vs_easy vs_hard binom sha_fast color"
echo "Processing Rust extraction"
for f in ${rust_examples}
do
    if [[ ! -e "$RUST_PATH/${f}.rs.out" ]]; then continue; fi
    mkdir -p $RUST_PATH/${f}-${RUST_SUFFIX_PATH}
    src_rust_fname=$RUST_PATH/${f}.rs.out
    tgt_rust_fname=$RUST_PATH/${f}-${RUST_SUFFIX}
    main_rust_name=$RUST_PATH/${f}.main
    echo "removing previous extraction: " ${tgt_rust_fname}
    rm -f ${tgt_rust_fname}
    echo Processing $src_rust_fname "--->" $tgt_rust_fname
    cat $src_rust_fname $main_rust_name | sed "/^Debug/d" > $tgt_rust_fname
done

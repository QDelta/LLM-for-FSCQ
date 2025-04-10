#!/bin/bash

# export LCOQ_MODEL=gemini-1.5-flash-002
# export LCOQ_MODEL=gemini-1.5-pro-002
# export LCOQ_MODEL=gpt-4o-mini-2024-07-18
# export LCOQ_MODEL=gpt-4o-2024-11-20

cd tiktoken-cli
cargo build --release
cd ..
export LCOQ_COUNT_TOKEN="$PWD/tiktoken-cli/target/release/tiktoken-cli"

eval $(opam env)
dune build --profile=release
LCOQ="$PWD/_build/install/default/bin/lCoq"

export LCOQ_MODEL="$1"
export LCOQ_HINT_RATE="$2"
export LCOQ_SAMPLE_RATE="$3"

if [[ "$LCOQ_MODEL" == *"gemini"* ]]; then
    make -C fscq/src J=16 vos
    COQC="$LCOQ strip-proof" make -C fscq/src J=16 proof
    COQC="$LCOQ gptf-gemini" make -C fscq/src vok
elif [[ "$LCOQ_MODEL" == *"gpt"* ]]; then
    make -C fscq/src J=16 vos
    COQC="$LCOQ strip-proof" make -C fscq/src J=16 proof
    COQC="$LCOQ gptf-openai" make -C fscq/src vok
else
    echo "Unknown model: $LCOQ_MODEL"
    exit 1
fi

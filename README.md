This is the artifact for HotOS 2025 paper: Can Large Language Models Verify System Software? A Case Study Using FSCQ as a Benchmark.

All the model-generated proofs used for evaluation are located in `generated` directory.

## Prepare

1. Pull FSCQ by `git submodule update --init --recursive`

2. Use OPAM, run
   ```
   opam install . --deps-only
   opam install coq
   opam install coq-serapi
   ```

3. Install Rust, make sure `cargo` is in your `$PATH`.

## Run

1. Set environment variable `OPENAI_API_KEY` or `GOOGLE_API_KEY` for OpenAI/Gemini API token.

2. Run `./run.sh <MODEL> <HINT_RATE> <SAMPLE_RATE>`
   For example, `./run.sh gpt-4o-2024-11-20 0.5 0.05`

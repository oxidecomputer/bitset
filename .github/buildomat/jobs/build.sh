#!/bin/bash
#:
#: name = "build"
#: variety = "basic"
#: target = "helios-2.0"
#: rust_toolchain = "nightly"

set -o errexit
set -o pipefail
set -o xtrace

cargo --version
rustc --version

banner "check"
cargo fmt -- --check
cargo clippy --all-targets -- --deny warnings

banner "test"
cargo install cargo-nextest
cargo nextest run

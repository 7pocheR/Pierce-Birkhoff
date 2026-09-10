#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# Bind the mathematical sources and verification programs to this release.
shasum -a 256 -c verification/source.sha256
lake build
lake env lean --trust=0 verification/Statements6.lean
lake env lean --trust=0 verification/TrustReplay6.lean
shasum -a 256 -c verification/source.sha256

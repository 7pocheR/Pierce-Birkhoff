#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
shasum -a 256 -c verification/source.sha256
lake build
lake env lean --trust=0 verification/Statements8.lean
lake env lean --trust=0 verification/Formula8.lean
lake env lean --trust=0 verification/TrustReplay8.lean
shasum -a 256 -c verification/source.sha256

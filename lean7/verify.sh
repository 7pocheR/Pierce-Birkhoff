#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# The manifest binds the mathematical sources and verification programs.
shasum -a 256 -c verification/source.sha256
lake build
lake env lean verification/Statements7.lean
lake env lean verification/TrustReplay7.lean

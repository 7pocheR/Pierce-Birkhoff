#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v rg >/dev/null

# Check the mathematical sources separately from the axiom-audit test module.
if rg -n --glob '*.lean' --glob '!Audit.lean' \
  '\b(sorry|admit|axiom|sorryAx|native_decide|unsafe|ofReduceBool|implemented_by|extern|macro|elab|set_option|opaque|initialize|attribute|csimp|run_cmd|run_elab)\b|skipKernelTC|#eval|^[[:space:]]*((local|scoped)[[:space:]]+)?(syntax|notation)\b' \
  PBCounterexample PBCounterexample.lean; then
  printf '%s\n' 'Disallowed proof-source construct detected.' >&2
  exit 1
else
  pb_scan_status=$?
  if [[ "$pb_scan_status" -ne 1 ]]; then
    exit "$pb_scan_status"
  fi
fi

# Sequential module checks limit peak memory use. The final library build also
# verifies that all modules selected by the project configuration are built.
for pb_module in \
  Basic Semialgebraic Function PolynomialTopology RationalSubstitution \
  GenericOrbitPoint RadialScalar RadialPolynomial Radial OrbitAlgebra \
  OrbitNormalization OrbitGeometry QuadraticForms QuadraticDecomposition \
  MatrixProjection OrbitProjection OrbitVanishing Perturbation SignTopology \
  Reindexing FiniteExpressions SignObstruction Main Audit; do
  lake --rehash --no-cache --log-level=error build "PBCounterexample.${pb_module}"
done
lake --rehash --no-cache --log-level=error build

# Run the axiom test even when its build artifact was already current.
lake env lean PBCounterexample/Audit.lean

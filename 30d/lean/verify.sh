#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v rg >/dev/null

# Check mathematical sources separately from verification-only programs.
# The narrowly allowed options change resource limits, not proof checking.
# The local simp attribute names only ordinary matrix-entry theorems.
if rg --pcre2 -n --glob '*.lean' --glob '!Audit.lean' \
  '\b(sorry|admit|axiom|sorryAx|native_decide|unsafe|ofReduceBool|ofReduceNat|implemented_by|extern|macro|elab|opaque|initialize|csimp|run_cmd|run_elab)\b|skipKernelTC|#eval|^[[:space:]]*((local|scoped)[[:space:]]+)?(syntax|notation)\b|\bset_option\b(?! (?:maxHeartbeats 0|maxRecDepth 10000) in$)|\battribute\b(?! \[local simp\] Matrix\.cons_val_two Matrix\.cons_val_three Matrix\.cons_val_four$)' \
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
  Reindexing FiniteExpressions SignObstruction Main Audit \
  PolynomialSelection Laplacian SymmetricFunction RationalGenericPoint \
  SymmetricGenericPoint SymmetricDecomposition SymmetricAlgebra \
  SymmetricGeometry SymmetricOrbitVanishing SymmetricPerturbation \
  SymmetricSignObstruction SymmetricMain Collaborator30Function \
  Collaborator30SignObstruction Collaborator30Main; do
  lake --rehash --no-cache --log-level=error build "PBCounterexample.${pb_module}"
done
lake --rehash --no-cache --log-level=error build

# Run the axiom test even when its build artifact was already current.
lake env lean PBCounterexample/Audit.lean
lake env lean verification/Statements30.lean
lake env lean verification/FoundationTypes30.lean
lake env lean verification/RawAudit30.lean

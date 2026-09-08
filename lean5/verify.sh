#!/usr/bin/env bash
# Rebuild the released sources and run the complete audit once.
set -euo pipefail
export LC_ALL=C

fail() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
[[ $# == 0 ]] || fail 'Usage: ./verify.sh (optional environment: PB5_VERIFY_TMPDIR)'
[[ $(uname -s) == Linux ]] || fail 'This reproducer requires Linux and GNU command-line tools.'
for command in elan git python3 sha256sum find sort xargs cmp tee; do
  command -v "$command" >/dev/null || fail "Required command not found: $command"
done
[[ -x /usr/bin/time ]] || fail 'GNU time is required at /usr/bin/time.'

package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
temporary_base=${PB5_VERIFY_TMPDIR:-/tmp}
[[ -d "$temporary_base" ]] || fail 'PB5_VERIFY_TMPDIR must name an existing directory.'
run=$(mktemp -d "$temporary_base/pb5-verification.XXXXXX")
run=$(cd -- "$run" && pwd -P)
case "$run:$package" in *$'\n'*|*$'\r'*) fail 'Paths must not contain line breaks.';; esac
[[ "$run" != *:* && "$package" != *:* ]] || fail 'Paths must not contain a colon.'
out="$run/logs"
source="$run/project"
dependencies="$run/dependencies"
mkdir -p "$out" "$source" "$dependencies"
trap 'rc=$?; printf "%s\n" "$rc" > "$out/task-exit-code"; printf "VERIFICATION_EXIT=%s RESULTS=%s\n" "$rc" "$run"' EXIT
exec > >(tee "$out/driver.log") 2>&1
printf 'VERIFICATION_DIRECTORY=%s\n' "$run"

# Ignore inherited Lean and dynamic-library paths. Only explicitly checked
# dependencies and the newly created output directory enter proof compilation.
unset LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT ELAN_TOOLCHAIN
unset LD_LIBRARY_PATH LD_PRELOAD DYLD_LIBRARY_PATH DYLD_INSERT_LIBRARIES
unset LEAN_OPTS LEAN_OPTIONS

mathematical_modules=(
  Basic FiniteExpressions Semialgebraic RadialScalar RadialPolynomial
  PolynomialSelection LatticeThreshold WeightedPolynomial Gram5Data
  Gram5Variations Gram5Differential Gram5Implicit Gram5Paths Gram5Selection
  Gram5Scaling Gram5PositivePaths Gram5FiniteTests Gram5LowWeights
  Gram5WeightedKernel Gram5LeafDecomposition Gram5LeafLimits Gram5FiniteFamily
  Gram5Degree Gram5Main
)
[[ ${#mathematical_modules[@]} == 24 ]] || fail 'Incorrect implementation inventory.'
project_targets=()
for module in "${mathematical_modules[@]}"; do project_targets+=("PBCounterexample/$module"); done
project_targets+=(PBCounterexample gram5_independent_contract_20260908
  gram5_independent_binding_20260908 gram5_independent_intermediate_binding_20260908
  gram5_independent_audit_tooling_20260908 gram5_independent_raw_trust_20260908
  gram5_independent_fresh_replay_20260908)
{
  printf './%s.lean\n' "${project_targets[@]}"
  printf './lakefile.toml\n./lake-manifest.json\n./lean-toolchain\n'
} | sort > "$out/expected-source-files.txt"
sed 's/^[0-9a-f]*  //' "$package/verification/source.sha256" | sort > "$out/manifest-source-files.txt"
cmp "$out/expected-source-files.txt" "$out/manifest-source-files.txt"
[[ ! -e "$package/.lake" && ! -L "$package/.lake" && ! -e "$package/build" && ! -L "$package/build" ]] ||
  fail 'Use a clean release directory without .lake or build outputs.'
[[ -z $(find "$package" -type l -print -quit) ]] || fail 'Release files must not be symbolic links.'
[[ -z $(find "$package" -type f \( -name '*.olean' -o -name '*.ilean' -o -name '*.o' \) -print -quit) ]] ||
  fail 'The release directory contains compiled artifacts.'
(cd "$package" && sha256sum -c verification/source.sha256) > "$out/release-source-before.log"
while IFS= read -r file; do
  mkdir -p "$source/$(dirname "$file")"
  cp -- "$package/$file" "$source/$file"
done < "$out/expected-source-files.txt"
(cd "$source" && find . -type f -print | sort) > "$out/actual-source-files.txt"
cmp "$out/expected-source-files.txt" "$out/actual-source-files.txt"
(cd "$source" && sha256sum -c "$package/verification/source.sha256") > "$out/source-before.log"
cp -- "$source/lean-toolchain" "$source/lakefile.toml" "$source/lake-manifest.json" "$dependencies/"
printf '%s\n' "${project_targets[@]}" > "$out/project-module-order.txt"
printf 'FRESH_PROJECT_HAS_NO_COMPILED_ARTIFACTS\n'

# Resolve every Git dependency from the frozen manifest, never by a branch name.
python3 - "$source/lake-manifest.json" > "$out/dependency-pins.tsv" <<'PY'
import json, re, sys
with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
expected = {"Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
            "LeanSearchClient", "plausible", "mathlib"}
packages = manifest["packages"]
if len(packages) != len(expected) or {p["name"] for p in packages} != expected:
    raise SystemExit("Unexpected dependency inventory")
for p in packages:
    if (p["type"] != "git" or p.get("subDir") is not None
            or not re.fullmatch(r"[0-9a-f]{40}", p["rev"])
            or not p["url"].startswith("https://github.com/")
            or any(c in p["url"] for c in "\t\r\n")):
        raise SystemExit("Unexpected dependency specification")
    if p["name"] == "mathlib" and p["rev"] != "ffbfefaec67d01d561affd800125a281db8bb7f3":
        raise SystemExit("Unexpected Mathlib revision")
    print(p["name"], p["rev"], p["url"], sep="\t")
PY
cd "$dependencies"
toolchain=$(< lean-toolchain)
[[ "$toolchain" == leanprover/lean4:v4.34.0-rc1 ]] || fail 'Unexpected Lean toolchain.'
elan toolchain install "$toolchain" > "$out/toolchain-install.log" 2>&1
lean_executable=$(elan which lean)
lake_executable=$(elan which lake)
toolchain_root=$(cd -- "$(dirname -- "$lean_executable")/.." && pwd -P)
[[ "$lake_executable" == "$toolchain_root/bin/lake" ]] || fail 'Lean and Lake use different toolchains.'
"$lean_executable" --version > "$out/toolchain.log"
grep -F 'version 4.34.0-rc1,' "$out/toolchain.log"
grep -F 'commit 3447a668783dbce1a8fdb97101dd067687b2b418' "$out/toolchain.log"
while IFS=$'\t' read -r name revision url; do
  destination="$dependencies/.lake/packages/$name"
  git init -q "$destination"
  git -C "$destination" remote add origin "$url"
  git -C "$destination" fetch --depth=1 origin "$revision" > "$out/fetch-$name.log" 2>&1
  git -C "$destination" checkout --detach FETCH_HEAD >> "$out/fetch-$name.log" 2>&1
  [[ $(git -C "$destination" rev-parse HEAD) == "$revision" ]] || fail "Wrong revision: $name"
done < "$out/dependency-pins.tsv"

# This command prepares foreign dependencies only. The bootstrap directory
# contains no mathematical project sources and is never a project import path.
"$lake_executable" exe cache get > "$out/dependency-cache.log" 2>&1
for file in lean-toolchain lakefile.toml lake-manifest.json; do
  cmp "$dependencies/$file" "$source/$file"
done
check_dependency_sources() {
  while IFS=$'\t' read -r name revision url; do
    destination="$dependencies/.lake/packages/$name"
    [[ $(git -C "$destination" rev-parse HEAD) == "$revision" ]] || fail "Changed dependency revision: $name"
    [[ -z $(git -C "$destination" status --porcelain --untracked-files=normal) ]] ||
      fail "Changed or untracked dependency sources: $name"
    printf 'PINNED_DEPENDENCY_OK %s %s %s\n' "$name" "$revision" "$url"
  done < "$out/dependency-pins.tsv"
}
check_dependency_sources > "$out/dependency-sources-before.log"

foreign_paths=("$toolchain_root/lib/lean")
artifact_paths=("$toolchain_root")
artifact_labels=(toolchain)
for name in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  artifact="$dependencies/.lake/packages/$name/.lake/build/lib"
  if [[ "$name" == Cli && ! -e "$artifact" ]]; then mkdir -p "$artifact/lean"; fi
  [[ -d "$artifact/lean" ]] || fail "Missing dependency artifacts: $name"
  foreign_paths+=("$artifact/lean")
  artifact_paths+=("$artifact")
  artifact_labels+=("package-$name")
done
check_foreign_paths() {
  for foreign in "${foreign_paths[@]}"; do
    [[ ! -e "$foreign/PBCounterexample" && ! -L "$foreign/PBCounterexample" ]] || fail "Project namespace in $foreign"
    for target in "${project_targets[@]}"; do
      [[ ! -e "$foreign/$target.olean" && ! -L "$foreign/$target.olean" ]] || fail "Project import shadow in $foreign: $target"
    done
    printf 'NO_PROJECT_IMPORT_OVERRIDE %s\n' "$foreign"
  done
}
check_foreign_paths > "$out/foreign-project-exclusion-before.log"
# Record both file contents and the complete artifact inventory. This is a new
# reproduction's artifact identity, not an assertion of identical cache bytes
# across operating systems or separately generated dependency builds.
for i in "${!artifact_paths[@]}"; do
  artifact=${artifact_paths[$i]}
  label=${artifact_labels[$i]}
  (cd "$artifact" && find . -type f -print | sort) > "$out/$label-files.txt"
  (cd "$artifact" && find . -type f -print0 | sort -z | xargs -0 -r sha256sum) > "$out/$label.sha256"
done

cd "$source"
[[ ! -e "$run/build" ]] || fail 'Project output directory already exists.'
mkdir -p "$run/build/PBCounterexample"
export LEAN_SYSROOT="$toolchain_root"
export LEAN_PATH="$run/build"
export LD_LIBRARY_PATH="$toolchain_root/lib:$toolchain_root/lib/lean"
for name in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  LEAN_PATH+=":$dependencies/.lake/packages/$name/.lake/build/lib/lean"
  LD_LIBRARY_PATH+=":$dependencies/.lake/packages/$name/.lake/build/lib"
done
LEAN_PATH+=":$toolchain_root/lib/lean"
printf 'LEAN_EXECUTABLE=%s\nLEAN_SYSROOT=%s\nLEAN_PATH=%s\nLD_LIBRARY_PATH=%s\n' \
  "$lean_executable" "$LEAN_SYSROOT" "$LEAN_PATH" "$LD_LIBRARY_PATH" > "$out/environment.log"
compile_source() {
  local target=$1 label=${1//\//_} rc=0
  printf 'BEGIN %s %s\n' "$(date -u +%FT%TZ)" "$target"
  cmp "$target.lean" "$package/$target.lean"
  printf '%q ' "$lean_executable" --trust=0 -j 4 -o "$run/build/$target.olean" "$target.lean" > "$out/$label-command.txt"
  printf '\n' >> "$out/$label-command.txt"
  /usr/bin/time -v "$lean_executable" --trust=0 -j 4 -o "$run/build/$target.olean" "$target.lean" > "$out/$label.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$out/$label-exit-code"
  [[ "$rc" == 0 ]] || fail "Compilation failed: $target (see $out/$label.log)"
  if grep -Ei 'declaration uses .sorry.|failed to synthesize|unsolved goals' "$out/$label.log"; then
    fail "Unresolved proof diagnostic: $target"
  fi
  cmp "$target.lean" "$package/$target.lean"
  printf 'END %s %s rc=0\n' "$(date -u +%FT%TZ)" "$target"
}
for module in "${mathematical_modules[@]}"; do compile_source "PBCounterexample/$module"; done
for target in PBCounterexample gram5_independent_contract_20260908 \
    gram5_independent_binding_20260908 gram5_independent_intermediate_binding_20260908 \
    gram5_independent_audit_tooling_20260908; do
  compile_source "$target"
done
printf '0\n' > "$out/source-build-exit-code"
printf 'SOURCE_FRESH_BUILD_PASS %s math_modules=24 independent_math_modules=3 wrapper=1 audit_tool=1\n' "$(date -u +%FT%TZ)"

# The unchanged entry runs runAudit true: raw checks and one full kernel replay.
printf 'BEGIN %s complete-raw-and-empty-kernel-audit\n' "$(date -u +%FT%TZ)"
audit_rc=0
printf '%q ' "$lean_executable" --trust=0 -j 4 gram5_independent_fresh_replay_20260908.lean > "$out/complete-audit-command.txt"
printf '\n' >> "$out/complete-audit-command.txt"
/usr/bin/time -v "$lean_executable" --trust=0 -j 4 gram5_independent_fresh_replay_20260908.lean > "$out/complete-audit.log" 2>&1 || audit_rc=$?
printf '%s\n' "$audit_rc" > "$out/complete-audit-exit-code"
[[ "$audit_rc" == 0 ]] || fail "Complete audit failed (see $out/complete-audit.log)"
python3 "$package/verification/check_audit_log.py" "$out/complete-audit.log"
printf 'END %s complete-raw-and-empty-kernel-audit rc=0\n' "$(date -u +%FT%TZ)"

(cd "$source" && sha256sum -c "$package/verification/source.sha256") > "$out/source-after.log"
(cd "$package" && sha256sum -c verification/source.sha256) > "$out/release-source-after.log"
check_dependency_sources > "$out/dependency-sources-after.log"
check_foreign_paths > "$out/foreign-project-exclusion-after.log"
for i in "${!artifact_paths[@]}"; do
  artifact=${artifact_paths[$i]}
  label=${artifact_labels[$i]}
  (cd "$artifact" && find . -type f -print | sort) > "$out/$label-files-after.txt"
  cmp "$out/$label-files.txt" "$out/$label-files-after.txt"
  if [[ -s "$out/$label.sha256" ]]; then
    (cd "$artifact" && sha256sum -c "$out/$label.sha256") > "$out/$label-check-after.log"
  fi
done
printf 'FULL_VERIFICATION_TASK_EXIT=0\n'

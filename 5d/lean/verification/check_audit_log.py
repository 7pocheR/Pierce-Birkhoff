#!/usr/bin/env python3
"""Check completeness of the frozen audit program's output, without running Lean."""
import re
import sys


def check(text):
    def require(pattern, count=1):
        matches = re.findall(pattern, text, re.MULTILINE)
        if len(matches) != count:
            raise ValueError(f"Expected {count} occurrence(s): {pattern}; got {len(matches)}")
        return matches

    require(r"^GRAM5_PROJECT_INVENTORY_OK modules=27 all_project_names=932 safe_roots=932 records=932 duplicates=0 retained_proof_variants=0; unsafe_partial_exemptions=0$")
    require(r"^GRAM5_PROJECT_MODULE ", 27)
    require(r"^GRAM5_PROJECT_DECL ", 932)
    require(r"^GRAM5_CACHED_AXIOMS ", 932)
    require(r"^GRAM5_NEGATIVE_CONTROL_OK ", 13)
    require(r"^GRAM5_KERNEL_NEGATIVE_CONTROL_OK invalid proof rejected:.*$")
    require(r"^GRAM5_KERNEL_NEGATIVE_CONTROL_OK invalid alternate stored body rejected:.*$")
    require(r"^GRAM5_AUDIT_STAGE both kernel negative controls complete$")
    require(r"^GRAM5_AUDIT_STAGE empty trust-zero kernel replay begins$")
    require(r"^GRAM5_AUDIT_STAGE effective closure and all additional stored-proof dependencies replayed$")
    require(r"^GRAM5_AUDIT_STAGE every retained stored proof body kernel-checked$")
    for name, origin in [("propext", "Init.Core"), ("Classical.choice", "Init.Prelude"), ("Quot.sound", "Init.Core")]:
        require(r"^GRAM5_STANDARD_AXIOM_SCHEMA_OK " + re.escape(name) + " origin=" + re.escape(origin) + r" TYPE ")
    axioms = r"\[propext,\s*Classical\.choice,\s*Quot\.sound\]"
    require(r"^GRAM5_INDEPENDENT_RAW_AUDIT_OK roots=932 effective_constants=37358 combined_constants=37358 definitions=8144 theorems=27262 stored_proof_variants=0 axioms=" + axioms)
    require(r"^GRAM5_INDEPENDENT_EMPTY_KERNEL_REPLAY_OK roots=932 supplied_constants=37358 stored_proof_variants=0 axioms=" + axioms)
    roots = [
        "PBCounterexample.Gram5.whole_space_counterexample",
        "PBCounterexample.Gram5.exists_whole_space_counterexample",
        "PBCounterexample.Gram5.not_finite_sup_inf_polynomials",
        "PBCounterexample.Gram5.not_isPolynomialLattice",
        "PBCounterexample.Gram5.exists_finite_threshold_pair",
        "PBCounterexample.Gram5.exists_finite_threshold_paths",
        "PBCounterexample.Gram5.low_weight_kernel_formula",
        "PBCounterexample.Gram5.exists_implicitCorrection",
        "PBCounterexample.Gram5.LeafDecomposition.eventually_transfer_zero",
        "PBCounterexample.WeightedPolynomial.tendsto_eval_scale_div",
        "PBCounterexample.Gram5IndependentBinding.whole_space_claim",
        "PBCounterexample.Gram5IndependentBinding.finite_threshold_pair_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.complete_kernel_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.weighted_decomposition_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.weighted_evaluation_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.actual_ift_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.fixed_epsilon_continuity_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.exact_target_claim",
        "PBCounterexample.Gram5IndependentIntermediateBinding.weighted_finite_collection_claim",
    ]
    require(r"^GRAM5_FINAL_TYPE ", len(roots))
    for name in roots:
        require(r"^GRAM5_FINAL_TYPE " + re.escape(name) + " ")
    if re.search(r"declaration uses .sorry.|^.*:\d+:\d+: error:", text, re.MULTILINE | re.IGNORECASE):
        raise ValueError("Unresolved proof or compiler error diagnostic")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check_audit_log.py LOG_FILE")
    try:
        with open(sys.argv[1], encoding="utf-8") as stream:
            check(stream.read())
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print("COMPLETE_AUDIT_LOG_CHECK_OK")

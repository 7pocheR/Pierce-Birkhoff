import gram5_independent_audit_tooling_20260908

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftCoreM (Gram5IndependentAudit.runAudit true)

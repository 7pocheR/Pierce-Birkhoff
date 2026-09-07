import PBCounterexample.SymmetricMain
import PBCounterexample.Collaborator30Main
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Replay

set_option maxHeartbeats 0

open Lean

def rawDependencies30 (ci : ConstantInfo) : Array Name := Id.run do
  let mut result := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ value.getUsedConstants
  match ci with
  | .inductInfo v => result := result ++ v.ctors.toArray ++ v.all.toArray
  | .recInfo v => result := result ++ v.all.toArray
  | .ctorInfo v => result := result.push v.induct
  | _ => pure ()
  return result

open Lean

def standardFoundationTypes30 : Array (Name × List Name × Expr) := Id.run do
  let prop : Expr := .sort .zero
  let u : Level := .param `u
  let imp (n : Name) (t b : Expr) : Expr := .forallE n t b .implicit
  let arr (t b : Expr) : Expr := .forallE .anonymous t b .default
  let app2 (f a b : Expr) : Expr := .app (.app f a) b
  let app3 (f a b c : Expr) : Expr := .app (app2 f a b) c
  let pe := imp `a prop (imp `b prop
    (arr (app2 (.const ``Iff []) (.bvar 1) (.bvar 0))
      (app3 (.const ``Eq [.succ .zero]) prop (.bvar 2) (.bvar 1))))
  let ch := imp `α (.sort u)
    (arr (.app (.const ``Nonempty [u]) (.bvar 0)) (.bvar 1))
  let rel := arr (.bvar 0) (arr (.bvar 1) prop)
  let quotient := app2 (.const ``Quot [u]) (.bvar 4) (.bvar 3)
  let qa := app3 (.const ``Quot.mk [u]) (.bvar 4) (.bvar 3) (.bvar 2)
  let qb := app3 (.const ``Quot.mk [u]) (.bvar 4) (.bvar 3) (.bvar 1)
  let qs := imp `α (.sort u) (imp `r rel (imp `a (.bvar 1) (imp `b (.bvar 2)
    (arr (app2 (.bvar 2) (.bvar 1) (.bvar 0))
      (app3 (.const ``Eq [u]) quotient qa qb)))))
  return #[(``propext, [], pe), (``Classical.choice, [`u], ch), (``Quot.sound, [`u], qs)]

def checkStandardFoundationTypes30 : Elab.Command.CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  for (name, levels, expected) in standardFoundationTypes30 do
    let some (.axiomInfo ci) := env.checked.get.find? name
      | throwError "Expected a standard axiom declaration: {name}"
    unless ci.levelParams == levels do
      throwError "Unexpected universe parameters for {name}: {ci.levelParams}"
    unless ci.type == expected do
      throwError "Unexpected exact foundational axiom type for {name}: {ci.type}"
    logInfo m!"STANDARD_FOUNDATION_TYPE_OK {name} levels={ci.levelParams} type={ci.type}"

run_cmd do
  checkStandardFoundationTypes30
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[
    ``PBCounterexample.SymmetricMain.pierce_birkhoff_counterexample30,
    ``PBCounterexample.SymmetricMain.explicit_quadratic_counterexample30,
    ``PBCounterexample.SymmetricMain.no_finite_max_min_representation,
    ``PBCounterexample.Collaborator30Main.pierce_birkhoff_counterexample30,
    ``PBCounterexample.Collaborator30Main.explicit_quadratic_counterexample30,
    ``PBCounterexample.Collaborator30Main.no_finite_max_min_representation]
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut supplied : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := kenv.find? name | throwError "Missing dependency {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial mathematical dependency {name}"
    match ci with
    | .axiomInfo _ =>
      axioms := axioms.insert name
      unless allowed.contains name do throwError "Unexpected axiom {name}"
    | _ => pure ()
    supplied := supplied.insert name ci
    for dep in rawDependencies30 ci do
      unless seen.contains dep do pending := pending.push dep
  logInfo m!"THEOREM_REPLAY_START roots={roots} constants={supplied.size} axioms={axioms.toArray.qsort Name.lt}"
  let start ← IO.monoMsNow
  let empty ← mkEmptyEnvironment
  let checked ← empty.toKernelEnv.replay supplied
  for name in seen do
    let some original := kenv.find? name | throwError "Missing original {name}"
    let some verified := checked.find? name | throwError "Replay omitted {name}"
    unless original.type == verified.type && original.levelParams == verified.levelParams do
      throwError "Replay changed declaration type {name}"
  for name in roots do
    let some ci := checked.find? name | throwError "Replay omitted final root {name}"
    let axs ← collectAxioms name
    logInfo m!"CHECKED_FINAL_TYPE {name} {ci.type}"
    logInfo m!"CHECKED_FINAL_AXIOMS {name} {axs}"
  let finish ← IO.monoMsNow
  logInfo m!"FRESH_30D_THEOREM_KERNEL_REPLAY_OK roots={roots.size} constants={supplied.size} axioms={axioms.toArray.qsort Name.lt} milliseconds={finish-start}"

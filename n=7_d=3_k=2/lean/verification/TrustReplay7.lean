import PBCounterexample.Gram7Main
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Replay

open Lean

noncomputable section
universe u
example : ∀ {a b : Prop}, (a ↔ b) → a = b := @propext
example : ∀ {α : Sort u}, Nonempty α → α := @Classical.choice
example : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b := @Quot.sound
end

def rawDependencies7 (ci : ConstantInfo) : Array Name := Id.run do
  let mut result := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ value.getUsedConstants
  match ci with
  | .inductInfo v => result := result ++ v.ctors.toArray ++ v.all.toArray
  | .recInfo v => result := result ++ v.all.toArray
  | .ctorInfo v => result := result.push v.induct
  | _ => pure ()
  return result

run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let required : Array Name := #[
    ``PBCounterexample.Gram7.counterexample,
    ``PBCounterexample.Gram7.no_finite_max_min_representation,
    ``PBCounterexample.Gram7.pierce_birkhoff_fails_in_dimension_seven]
  let mut roots : Array Name := #[]
  let mut operational : Array Name := #[]
  let mut rootNames : NameSet := {}
  let mut seeds : Array Name := #[]
  let mut records : Nat := 0
  let mut duplicates : Nat := 0
  let mut reportedUnion : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let origin := env.header.moduleNames[i]!
    if (`PBCounterexample).isPrefixOf origin then
      logInfo m!"PROJECT_MODULE {origin}"
      for name in env.header.moduleData[i]!.constNames, stored in env.header.moduleData[i]!.constants do
        records := records + 1
        let some ci := kenv.find? name | throwError "Missing project declaration {name}"
        unless stored.name == name && stored.type == ci.type &&
            stored.levelParams == ci.levelParams do
          throwError "Stored declaration differs from imported declaration: {name}"
        if rootNames.contains name then
          duplicates := duplicates + 1
          unless stored.value? (allowOpaque := true) == ci.value? (allowOpaque := true) do
            throwError "Duplicate declaration body differs: {name}"
        if !(stored.isUnsafe || stored.isPartial) then
          seeds := seeds ++ rawDependencies7 stored
        if rootNames.contains name then continue
        rootNames := rootNames.insert name
        if ci.isUnsafe || ci.isPartial then
          operational := operational.push name
          logInfo m!"OPERATIONAL_PROJECT_DECL {origin} {name}"
          continue
        roots := roots.push name
        let axioms ← collectAxioms name
        for ax in axioms do reportedUnion := reportedUnion.insert ax
        logInfo m!"PROJECT_DECL {origin} {name} AXIOMS {axioms}"
  for (name, ci) in kenv.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if (`PBCounterexample).isPrefixOf origin && !rootNames.contains name then
        throwError "Project declaration omitted from module records: {origin} {name} {ci.type}"
  for name in required do
    unless roots.contains name do throwError "Missing required root {name}"
  let mut pending := roots ++ seeds
  let mut seen : NameSet := {}
  let mut rawAxioms : NameSet := {}
  let mut replayConstants : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := kenv.find? name | throwError "Missing dependency {name}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial mathematical dependency {name}"
    if ci.isAxiom then
      rawAxioms := rawAxioms.insert name
      unless allowed.contains name do throwError "Unexpected axiom {name}"
    replayConstants := replayConstants.insert name ci
    pending := pending ++ rawDependencies7 ci
  let raw := rawAxioms.toArray.qsort Name.lt
  unless raw == reportedUnion.toArray.qsort Name.lt do
    throwError "Raw and reported axiom sets differ"
  logInfo m!"RAW_AUDIT_OK roots={roots.size} dependencies={seen.size} records={records} duplicates={duplicates} operational={operational.size} axioms={raw}"
  let empty ← mkEmptyEnvironment
  let verified ← empty.toKernelEnv.replay replayConstants
  for name in seen do
    let some original := kenv.find? name | throwError "Missing original {name}"
    let some checked := verified.find? name | throwError "Replay omitted {name}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Replay changed declaration type: {name}"
  logInfo m!"EMPTY_KERNEL_REPLAY_OK roots={roots.size} dependencies={seen.size} axioms={raw}"
  let some (.thmInfo originalTheorem) := kenv.find? required[2]! |
    throwError "Final root is not a theorem"
  let wrongProof : Declaration := .thmDecl { originalTheorem with
    name := `Gram7Verification.invalidFinalProof
    value := mkConst ``True.intro
    all := [`Gram7Verification.invalidFinalProof] }
  match verified.addDeclCore 0 0 wrongProof (cancelTk? := none) with
  | .ok _ => throwError "Negative control accepted an invalid final proof"
  | .error _ => logInfo "NEGATIVE_CONTROL_INVALID_FINAL_PROOF_REJECTED"
  let missingValue : Declaration := .thmDecl { originalTheorem with
    name := `Gram7Verification.missingDependency
    value := mkConst `Gram7Verification.nonexistentProof
    all := [`Gram7Verification.missingDependency] }
  match verified.addDeclCore 0 0 missingValue (cancelTk? := none) with
  | .ok _ => throwError "Negative control accepted a nonexistent dependency"
  | .error _ => logInfo "NEGATIVE_CONTROL_MISSING_DEPENDENCY_REJECTED"
  let fakeAxiom : ConstantInfo := .axiomInfo {
    name := `Gram7Verification.unapprovedAxiom
    levelParams := []
    type := mkConst ``False
    isUnsafe := false }
  unless fakeAxiom.isAxiom && !allowed.contains fakeAxiom.name do
    throwError "Negative control failed to identify an unapproved axiom"
  logInfo "NEGATIVE_CONTROL_UNAPPROVED_AXIOM_IDENTIFIED"
  for name in required do
    let ci ← getConstInfo name
    logInfo m!"FINAL_TYPE {name} {ci.type}"

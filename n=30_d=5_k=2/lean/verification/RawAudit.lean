import PBCounterexample
import PBCounterexample.Audit
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean

def rawDependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut result := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ value.getUsedConstants
  match ci with
  | .inductInfo v => result := result ++ v.ctors.toArray ++ v.all.toArray
  | .recInfo v => result := result ++ v.all.toArray
  | .ctorInfo v => result := result.push v.induct
  | _ => pure ()
  return result

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  let mut operational : Array Name := #[]
  let mut rootNames : NameSet := {}
  let mut bodySeeds : Array Name := #[]
  let mut operationalBodySeeds : Array Name := #[]
  let mut recordCount : Nat := 0
  let mut duplicateCount : Nat := 0
  let mut reportedUnion : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let origin := env.header.moduleNames[i]!
    if (`PBCounterexample).isPrefixOf origin then
      for name in env.header.moduleData[i]!.constNames, stored in env.header.moduleData[i]!.constants do
        recordCount := recordCount + 1
        let some ci := kenv.find? name | throwError "Missing project declaration {name}"
        let some idx := env.getModuleIdxFor? name | throwError "Missing defining module for {name}"
        unless stored.name == name && stored.type == ci.type && stored.levelParams == ci.levelParams do
          throwError "Stored declaration differs from imported declaration: {name}"
        if idx.toNat != i then
          duplicateCount := duplicateCount + 1
          logInfo m!"DUPLICATE_MODULE_RECORD {name} stored={origin} firstOrigin={env.header.moduleNames[idx.toNat]!} kind={kind stored}"
        if stored.isUnsafe || stored.isPartial then
          operationalBodySeeds := operationalBodySeeds ++ rawDependencies stored
        else
          bodySeeds := bodySeeds ++ rawDependencies stored
        if rootNames.contains name then continue
        rootNames := rootNames.insert name
        let axs ← collectAxioms name
        if ci.isUnsafe || ci.isPartial then
          operational := operational.push name
          logInfo m!"OPERATIONAL_DECL {origin} {kind ci} {name} AXIOMS {axs} TYPE {ci.type}"
          continue
        roots := roots.push name
        for ax in axs do
          reportedUnion := reportedUnion.insert ax
        logInfo m!"PROJECT_DECL {origin} {kind ci} {name} AXIOMS {axs}"
  for (name, ci) in kenv.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if (`PBCounterexample).isPrefixOf origin && !rootNames.contains name then
        rootNames := rootNames.insert name
        let axs ← collectAxioms name
        if ci.isUnsafe || ci.isPartial then
          operational := operational.push name
          logInfo m!"EXTRA_OPERATIONAL_DECL {origin} {kind ci} {name} AXIOMS {axs} TYPE {ci.type}"
          continue
        roots := roots.push name
        for ax in axs do
          reportedUnion := reportedUnion.insert ax
        logInfo m!"EXTRA_PROJECT_DECL {origin} {kind ci} {name} AXIOMS {axs}"
  unless roots.contains ``PBCounterexample.pierce_birkhoff_counterexample do
    throwError "The final counterexample theorem was not included in the enumerated declarations"
  let mut pending := roots ++ bodySeeds
  let mut seen : NameSet := {}
  let mut rawAxioms : NameSet := {}
  let mut definitionCount : Nat := 0
  let mut theoremCount : Nat := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := kenv.find? name | throwError "Missing raw dependency {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial raw dependency {name}"
    match ci with
    | .axiomInfo _ =>
      rawAxioms := rawAxioms.insert name
      unless allowed.contains name do
        throwError "Unexpected RAW axiom {name}"
    | .thmInfo _ => theoremCount := theoremCount + 1
    | .defnInfo _ => definitionCount := definitionCount + 1
    | _ => pure ()
    for dep in rawDependencies ci do
      unless seen.contains dep do pending := pending.push dep
  let raw := rawAxioms.toArray.qsort Name.lt
  let reported := reportedUnion.toArray.qsort Name.lt
  unless raw == reported do
    throwError "Raw/report mismatch: {raw} versus {reported}"
  logInfo m!"RAW_AUDIT_OK roots={roots.size} visited={seen.size} definitions={definitionCount} theorems={theoremCount} axioms={raw} operational_roots={operational.size} records={recordCount} duplicates={duplicateCount}"
  let mut pendingOperational := operational ++ operationalBodySeeds
  let mut seenOperational : NameSet := {}
  let mut operationalAxioms : NameSet := {}
  while !pendingOperational.isEmpty do
    let name := pendingOperational.back!
    pendingOperational := pendingOperational.pop
    if seenOperational.contains name then continue
    seenOperational := seenOperational.insert name
    let some ci := kenv.find? name | throwError "Missing operational dependency {name}"
    if ci.isUnsafe || ci.isPartial then
      logInfo m!"UNSAFE_OPERATIONAL_DEPENDENCY {name}"
    match ci with
    | .axiomInfo _ => operationalAxioms := operationalAxioms.insert name
    | _ => pure ()
    for dep in rawDependencies ci do
      unless seenOperational.contains dep do pendingOperational := pendingOperational.push dep
  logInfo m!"OPERATIONAL_CLOSURE roots={operational.size} visited={seenOperational.size} axioms={operationalAxioms.toArray.qsort Name.lt}"
  for name in env.header.moduleNames do
    if (`PBCounterexample).isPrefixOf name then
      logInfo m!"PROJECT_MODULE {name}"
  for name in #[``PBCounterexample.pierce_birkhoff_counterexample,
      ``PBCounterexample.explicit_quadratic_counterexample72,
      ``PBCounterexample.no_finite_max_min_representation] do
    let ci ← getConstInfo name
    logInfo m!"FINAL_TYPE {name} {ci.type}"

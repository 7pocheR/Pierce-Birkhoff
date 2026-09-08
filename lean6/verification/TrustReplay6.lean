import PBCounterexample.Gram6Main
import Lean.Util.CollectAxioms
import Lean.Replay
import Lean.Compiler.Old
import Lean.Compiler.NoncomputableAttr

/-!
Independent executable checks for the six-dimensional import closure.
These checks are audit tools and are not dependencies of the mathematical theorem.
-/

open Lean

namespace Gram6IndependentAudit

def expectedProjectModules : Array Name := #[
  `PBCounterexample.Basic,
  `PBCounterexample.FiniteExpressions,
  `PBCounterexample.Gram6Coordinates,
  `PBCounterexample.Gram6CorrectionCoordinates,
  `PBCounterexample.Gram6Curve,
  `PBCounterexample.Gram6DeterminantVariations,
  `PBCounterexample.Gram6FiniteParameters,
  `PBCounterexample.Gram6Function,
  `PBCounterexample.Gram6Implicit,
  `PBCounterexample.Gram6Kernel,
  `PBCounterexample.Gram6LocalPaths,
  `PBCounterexample.Gram6Main,
  `PBCounterexample.Gram6MonomialKernel,
  `PBCounterexample.Gram6Polarization,
  `PBCounterexample.Gram6QuadraticCoordinates,
  `PBCounterexample.Gram6SignObstruction,
  `PBCounterexample.Gram6Variations,
  `PBCounterexample.GramSelection,
  `PBCounterexample.Laplacian,
  `PBCounterexample.LowDegreeCoordinates,
  `PBCounterexample.PolynomialSelection,
  `PBCounterexample.PolynomialSubstitution,
  `PBCounterexample.QuadraticForms,
  `PBCounterexample.Radial,
  `PBCounterexample.RadialPolynomial,
  `PBCounterexample.RadialScalar,
  `PBCounterexample.RadialTests,
  `PBCounterexample.Semialgebraic,
  `PBCounterexample.SignTopology]

def finalRoots : Array Name := #[
  ``PBCounterexample.Gram6.whole_space_counterexample,
  ``PBCounterexample.Gram6.exists_whole_space_counterexample,
  ``PBCounterexample.Gram6.not_finite_sup_inf_polynomials,
  ``PBCounterexample.Gram6.not_isPolynomialLattice,
  ``PBCounterexample.Gram6.exists_same_homogeneous_signs_different_f,
  ``PBCounterexample.Gram6.exists_opposite_corrected_gram_paths,
  ``PBCounterexample.Gram6.homogeneous_quadratic_original_kernel_iff,
  ``PBCounterexample.homogeneous_lattice_finite_homogeneous_sign_condition]

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Explicit syntax traversal; this does not use cached axiom data or Expr.foldConsts. -/
def expressionConstants (root : Expr) : NameSet := Id.run do
  let mut pending : Array Expr := #[root]
  let mut visited : Std.HashSet Expr := {}
  let mut result : NameSet := {}
  while !pending.isEmpty do
    let e := pending.back!
    pending := pending.pop
    if visited.contains e then continue
    visited := visited.insert e
    match e with
    | .forallE _ domain body _ | .lam _ domain body _ =>
      pending := pending.push domain |>.push body
    | .letE _ type value body _ =>
      pending := pending.push type |>.push value |>.push body
    | .app fn arg => pending := pending.push fn |>.push arg
    | .mdata _ body => pending := pending.push body
    | .proj name _ body =>
      result := result.insert name
      pending := pending.push body
    | .const name _ => result := result.insert name
    | _ => pure ()
  return result

def rawDependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut result := (expressionConstants ci.type).toArray
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (expressionConstants value).toArray
  match ci with
  | .inductInfo v => result := result ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => result := result.push v.induct
  | .recInfo v =>
    result := result ++ v.all.toArray
    for rule in v.rules do
      result := result.push rule.ctor ++ (expressionConstants rule.rhs).toArray
  | _ => pure ()
  return result

/-- Compare all stored logical information, including theorem and opaque bodies. -/
def sameDeclaration (a b : ConstantInfo) : Bool :=
  a.toConstantVal == b.toConstantVal &&
  match a, b with
  | .axiomInfo x, .axiomInfo y => x == y
  | .defnInfo x, .defnInfo y => x == y
  | .thmInfo x, .thmInfo y => x == y
  | .opaqueInfo x, .opaqueInfo y => x == y
  | .ctorInfo x, .ctorInfo y => x == y
  | .recInfo x, .recInfo y => x == y
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices &&
    x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
    x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .quotInfo x, .quotInfo y =>
    match x.kind, y.kind with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false
  | _, _ => false

/-- An unequal record is retained only when its sole possible difference is a
theorem body. This classifies additional verification work, not acceptance. -/
def storedTheoremVariant? (stored effective : ConstantInfo) :
    Except String (Option TheoremVal) := do
  if sameDeclaration stored effective then return none
  match stored, effective with
  | .thmInfo x, .thmInfo y =>
    unless x.toConstantVal == y.toConstantVal && x.all == y.all do
      throw "stored theorem differs in non-body fields"
    return some x
  | _, _ => throw "stored declaration differs outside the theorem-body case"

structure StoredTheoremVariant where
  origin : Name
  info : TheoremVal

structure ProjectInventory where
  roots : Array Name := #[]
  variants : Array StoredTheoremVariant := #[]
  operational : Array Name := #[]

structure OperationalSpec where
  name : Name
  parent : Name
  origin : Name
  noncomputableFlag : Bool

/-- Exactly the two separately generated implementations found in this frozen
closure. A suffix is not an authorization, and these are never proof roots. -/
def operationalSpecs : Array OperationalSpec := #[
  { name := `PBCounterexample.LatticeExpr.evalWith._unsafe_rec
    parent := `PBCounterexample.LatticeExpr.evalWith
    origin := `PBCounterexample.Radial
    noncomputableFlag := false },
  { name := `PBCounterexample.LatticeExpr.leaves._unsafe_rec
    parent := `PBCounterexample.LatticeExpr.leaves
    origin := `PBCounterexample.Radial
    noncomputableFlag := true }]

def operationalSpec? (name : Name) : Option OperationalSpec :=
  operationalSpecs.find? (fun spec => spec.name == name)

def registeredOrigin (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Full record accounting for these compiler implementations, not permission
to use them in a mathematical dependency graph. Raw safety rejection below is
unchanged. The generator is addAndCompilePartialRec in pinned Lean sources. -/
def checkOperationalRecord (lookup : Name → Option ConstantInfo)
    (originOf : Name → Option Name) (noncomputableOf : Name → Bool)
    (storedOrigin : Name) (stored effective : ConstantInfo) :
    Except String OperationalSpec := do
  let some spec := operationalSpec? stored.name
    | throw s!"unrecognized operational declaration: {stored.name}"
  unless storedOrigin == spec.origin && originOf spec.name == some spec.origin do
    throw "operational declaration has an unexpected module origin"
  unless sameDeclaration stored effective do
    throw "operational stored/effective records differ, including body"
  let .defnInfo value := stored
    | throw "operational record is not a definition"
  unless value.safety == .partial && !stored.isUnsafe && stored.isPartial do
    throw "operational record has unexpected safety"
  unless value.hints == .opaque && value.all == [spec.name] &&
      value.levelParams == [`u_1] do
    throw "operational record has unexpected definition metadata"
  unless Compiler.mkUnsafeRecName spec.parent == spec.name do
    throw "operational specification disagrees with compiler naming"
  unless noncomputableOf spec.name == spec.noncomputableFlag do
    throw "operational record has an unexpected noncomputable flag"
  if value.type.hasMVar || value.type.hasFVar || value.type.hasLooseBVars ||
      value.value.hasMVar || value.value.hasFVar || value.value.hasLooseBVars then
    throw "operational record has an open type or body"
  let some (.defnInfo parent) := lookup spec.parent
    | throw "operational record lacks its exact definition parent"
  unless parent.name == spec.parent && parent.safety == .safe do
    throw "operational parent is not the required safe definition"
  unless originOf spec.parent == some spec.origin && !noncomputableOf spec.parent do
    throw "operational parent has unexpected origin or noncomputable metadata"
  unless value.type == parent.type && value.levelParams == parent.levelParams do
    throw "operational type or universes differ from the safe parent"
  return spec

def auditStage (message : String) : CoreM Unit :=
  Lean.Core.liftIOCore do
    let out ← IO.getStdout
    out.putStrLn s!"GRAM6_AUDIT_STAGE {message}"
    out.flush

/-- The exact logical schemas from Init.Prelude and Init.Core, with bound variable
names ignored by Expr equality. Universe arity is checked separately. -/
def standardAxiomType (name : Name) (levels : List Name) : Option Expr := do
  if name == ``propext then
    if !levels.isEmpty then none else
      some <| mkForall `a .implicit (mkSort .zero) <|
        mkForall `b .implicit (mkSort .zero) <|
          mkForall `h .default
            (mkApp2 (mkConst ``Iff) (mkBVar 1) (mkBVar 0))
            (mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) (mkBVar 2) (mkBVar 1))
  else if name == ``Classical.choice then
    match levels with
    | [uName] =>
      let u := Level.param uName
      some <| mkForall `α .implicit (mkSort u) <|
        mkForall `h .default (mkApp (mkConst ``Nonempty [u]) (mkBVar 0)) (mkBVar 1)
    | _ => none
  else if name == ``Quot.sound then
    match levels with
    | [uName] =>
      let u := Level.param uName
      let relationType := mkForall `x .default (mkBVar 0) <|
        mkForall `y .default (mkBVar 1) (mkSort .zero)
      let premise := mkApp2 (mkBVar 2) (mkBVar 1) (mkBVar 0)
      let quotient := mkApp2 (mkConst ``Quot [u]) (mkBVar 4) (mkBVar 3)
      let left := mkApp3 (mkConst ``Quot.mk [u]) (mkBVar 4) (mkBVar 3) (mkBVar 2)
      let right := mkApp3 (mkConst ``Quot.mk [u]) (mkBVar 4) (mkBVar 3) (mkBVar 1)
      some <| mkForall `α .implicit (mkSort u) <|
        mkForall `r .implicit relationType <|
          mkForall `a .implicit (mkBVar 1) <|
            mkForall `b .implicit (mkBVar 2) <|
              mkForall `h .default premise
                (mkApp3 (mkConst ``Eq [u]) quotient left right)
    | _ => none
  else none

def standardAxiomOrigin (name : Name) : Option Name :=
  if name == ``Classical.choice then some `Init.Prelude
  else if name == ``propext || name == ``Quot.sound then some `Init.Core
  else none

def checkAxiom (a : AxiomVal) : Except String Unit := do
  let some expected := standardAxiomType a.name a.levelParams
    | throw s!"unexpected axiom or universe arity: {a.name}"
  unless !a.isUnsafe && a.type == expected do
    throw s!"nonstandard axiom type: {a.name}"

structure Trace where
  constants : Std.HashMap Name ConstantInfo := {}
  axioms : NameSet := {}
  definitions : Nat := 0
  theorems : Nat := 0

def traceDependencies (lookup : Name → Option ConstantInfo)
    (roots : Array Name) : Except String Trace := do
  let mut pending := roots
  let mut result : Trace := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if result.constants.contains name then continue
    let some ci := lookup name | throw s!"missing raw dependency: {name}"
    unless ci.name == name do throw s!"dependency name mismatch: {name}"
    if ci.isUnsafe || ci.isPartial then
      throw s!"unsafe or partial dependency: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throw s!"open or unresolved declaration type: {name}"
    if let some value := ci.value? (allowOpaque := true) then
      if value.hasMVar || value.hasFVar || value.hasLooseBVars then
        throw s!"open or unresolved declaration body: {name}"
    match ci with
    | .axiomInfo a =>
      checkAxiom a
      result := { result with axioms := result.axioms.insert name }
    | .defnInfo _ => result := { result with definitions := result.definitions + 1 }
    | .thmInfo _ => result := { result with theorems := result.theorems + 1 }
    | _ => pure ()
    result := { result with constants := result.constants.insert name ci }
    pending := pending ++ rawDependencies ci
  return result

def expectRejected {α : Type} (label fragment : String) (result : Except String α) :
    CoreM Unit := do
  match result with
  | .ok _ => throwError "Negative control was accepted: {label}"
  | .error reason =>
    unless reason.contains fragment do
      throwError "Negative control failed for an unintended reason: {label}: {reason}"
    logInfo m!"GRAM6_NEGATIVE_CONTROL_OK {label}: {reason}"

/-- Traverse the stored proof, overriding its own name with that exact record.
Reject every cycle back to the original name before any fresh-name checking. -/
def traceStoredVariant (lookup : Name → Option ConstantInfo) (info : TheoremVal) :
    Except String Trace := do
  let stored : ConstantInfo := .thmInfo info
  let result ← traceDependencies
    (fun name => if name == info.name then some stored else lookup name) #[info.name]
  for (_, dependency) in result.constants.toList do
    if (rawDependencies dependency).contains info.name then
      throw s!"stored theorem variant depends on its original name: {info.name}"
  return result

def negativeControls (kenv : Kernel.Environment) : CoreM Unit := do
  let unknown : ConstantInfo := .axiomInfo {
    name := `Gram6AuditNegative.hiddenAxiom
    levelParams := []
    type := mkConst ``True
    isUnsafe := false }
  let lookupUnknown : Name → Option ConstantInfo :=
    fun name => if name == unknown.name then some unknown else kenv.find? name
  expectRejected "new axiom" "unexpected axiom"
    (traceDependencies lookupUnknown #[unknown.name])
  let hidden : ConstantInfo := .thmInfo {
    name := `Gram6AuditNegative.hiddenProofDependency
    levelParams := []
    type := mkConst ``True
    value := mkConst unknown.name }
  let lookupHidden : Name → Option ConstantInfo := fun name =>
    if name == hidden.name then some hidden else lookupUnknown name
  expectRejected "axiom only in proof body" "unexpected axiom"
    (traceDependencies lookupHidden #[hidden.name])
  let missing : ConstantInfo := .thmInfo {
    name := `Gram6AuditNegative.missingProofDependency
    levelParams := []
    type := mkConst ``True
    value := mkConst `Gram6AuditNegative.doesNotExist }
  let lookupMissing : Name → Option ConstantInfo :=
    fun name => if name == missing.name then some missing else kenv.find? name
  expectRejected "missing proof dependency" "missing raw dependency"
    (traceDependencies lookupMissing #[missing.name])
  let wrongType : AxiomVal := {
    name := ``propext
    levelParams := []
    type := mkConst ``False
    isUnsafe := false }
  expectRejected "standard name with altered type" "nonstandard axiom type"
    (checkAxiom wrongType)
  let wrongUniverses : AxiomVal := {
    wrongType with levelParams := [`u] }
  expectRejected "standard name with altered universe arity" "unexpected axiom"
    (checkAxiom wrongUniverses)
  for safety in [DefinitionSafety.unsafe, DefinitionSafety.partial] do
    let bad : ConstantInfo := .defnInfo {
      name := `Gram6AuditNegative.operationalRoot
      levelParams := []
      type := mkConst ``True
      value := mkConst ``True.intro
      hints := .opaque
      safety := safety }
    let lookup : Name → Option ConstantInfo :=
      fun name => if name == bad.name then some bad else kenv.find? name
    expectRejected s!"excluded declaration safety {repr safety}" "unsafe or partial"
      (traceDependencies lookup #[bad.name])
  let expectedNames : Array Name := #[
    `Gram6AuditNegative.domain, `Gram6AuditNegative.letType,
    `Gram6AuditNegative.letValue, `Gram6AuditNegative.lambdaDomain,
    `Gram6AuditNegative.function, `Gram6AuditNegative.projectedType,
    `Gram6AuditNegative.argument]
  let expression :=
    mkForall `x .default (mkConst expectedNames[0]!) <|
      .letE `y (mkConst expectedNames[1]!) (mkConst expectedNames[2]!)
        (.lam `z (mkConst expectedNames[3]!)
          (.mdata {} (.app (mkConst expectedNames[4]!)
            (.proj expectedNames[5]! 0 (mkConst expectedNames[6]!)))) .default) false
  let actual := (expressionConstants expression).toArray.qsort Name.lt
  unless actual == expectedNames.qsort Name.lt do
    throwError "Expression traversal coverage control failed: {actual}"
  logInfo "GRAM6_NEGATIVE_CONTROL_OK every expression-bearing syntax position was traversed"
  let original := kenv.find? ``PBCounterexample.Gram6.whole_space_counterexample
  let some (.thmInfo original) := original
    | throwError "Final theorem is not a theorem declaration"
  let changed : ConstantInfo := .thmInfo { original with value := mkConst ``True.intro }
  unless !sameDeclaration (.thmInfo original) changed do
    throwError "Stored proof body comparison accepted an altered final theorem"
  logInfo "GRAM6_NEGATIVE_CONTROL_OK altered stored theorem body is detected by exact comparison"
  expectRejected "stored theorem with changed type" "non-body fields"
    (storedTheoremVariant? (.thmInfo { original with type := mkConst ``True })
      (.thmInfo original))
  let wrongKind : ConstantInfo := .axiomInfo {
    name := original.name
    levelParams := original.levelParams
    type := original.type
    isUnsafe := false }
  expectRejected "stored theorem replaced by an axiom" "outside the theorem-body case"
    (storedTheoremVariant? wrongKind (.thmInfo original))
  let selfReference : TheoremVal := {
    name := `Gram6AuditNegative.circularStoredVariant
    levelParams := []
    type := mkConst ``True
    value := mkConst `Gram6AuditNegative.circularStoredVariant }
  expectRejected "stored proof refers back to its original name" "depends on its original name"
    (traceStoredVariant kenv.find? selfReference)
  let bodyOnlyAxiom : TheoremVal := {
    selfReference with
    name := `Gram6AuditNegative.storedVariantHiddenAxiom
    value := mkConst unknown.name }
  expectRejected "new axiom in an alternate stored proof" "unexpected axiom"
    (traceStoredVariant lookupUnknown bodyOnlyAxiom)

/-- The finite operational classification must not become a name-based safety
bypass. Exercise its metadata gates and the unchanged mathematical traversal. -/
def operationalNegativeControls (env : Environment) : CoreM Unit := do
  let kenv := env.checked.get
  let originOf := registeredOrigin env
  let flags := fun name => isNoncomputable env name
  for spec in operationalSpecs do
    let some (.defnInfo original) := kenv.find? spec.name
      | throwError "Missing definition needed for operational controls: {spec.name}"
    let some (.defnInfo parent) := kenv.find? spec.parent
      | throwError "Missing safe parent needed for operational controls: {spec.parent}"
    let originalCI := ConstantInfo.defnInfo original
    let check := checkOperationalRecord kenv.find? originOf flags spec.origin
    match check originalCI originalCI with
    | .error reason => throwError "Actual operational metadata failed before controls: {reason}"
    | .ok _ => pure ()
    let rejectBoth := fun (label fragment : String) (changed : DefinitionVal) =>
      expectRejected s!"{spec.name}: {label}" fragment
        (check (.defnInfo changed) (.defnInfo changed))
    rejectBoth "lookalike operational name" "unrecognized operational"
      { original with name := `Gram6AuditNegative.lookalike._unsafe_rec }
    rejectBoth "operational record changed to unsafe" "unexpected safety"
      { original with safety := .unsafe }
    rejectBoth "operational record changed to safe" "unexpected safety"
      { original with safety := .safe }
    rejectBoth "operational reduction hints changed" "definition metadata"
      { original with hints := .abbrev }
    rejectBoth "operational mutual-declaration metadata changed" "definition metadata"
      { original with all := [] }
    rejectBoth "operational universe parameters changed" "definition metadata"
      { original with levelParams := [] }
    rejectBoth "operational type changed" "differ from the safe parent"
      { original with type := mkConst ``Nat }
    let wrongKind : ConstantInfo := .axiomInfo {
      name := original.name, levelParams := original.levelParams,
      type := original.type, isUnsafe := false }
    expectRejected s!"{spec.name}: operational declaration kind changed" "not a definition"
      (check wrongKind wrongKind)
    expectRejected s!"{spec.name}: changed stored operational body" "records differ, including body"
      (check (.defnInfo { original with value := mkConst ``Nat.zero }) originalCI)
    expectRejected s!"{spec.name}: changed stored module" "unexpected module origin"
      (checkOperationalRecord kenv.find? originOf flags `PBCounterexample.Basic
        originalCI originalCI)
    expectRejected s!"{spec.name}: missing parent" "lacks its exact definition parent"
      (checkOperationalRecord
        (fun name => if name == spec.parent then none else kenv.find? name)
        originOf flags spec.origin originalCI originalCI)
    for safety in [DefinitionSafety.unsafe, DefinitionSafety.partial] do
      expectRejected s!"{spec.name}: parent safety {repr safety}" "required safe definition"
        (checkOperationalRecord
          (fun name => if name == spec.parent then
            some (.defnInfo { parent with safety := safety }) else kenv.find? name)
          originOf flags spec.origin originalCI originalCI)
    expectRejected s!"{spec.name}: changed parent module" "parent has unexpected origin"
      (checkOperationalRecord kenv.find?
        (fun name => if name == spec.parent then some `PBCounterexample.Basic else originOf name)
        flags spec.origin originalCI originalCI)
    expectRejected s!"{spec.name}: changed operational noncomputable flag" "unexpected noncomputable flag"
      (checkOperationalRecord kenv.find? originOf
        (fun name => if name == spec.name then !flags name else flags name)
        spec.origin originalCI originalCI)
    expectRejected s!"{spec.name}: changed parent noncomputable flag" "parent has unexpected origin"
      (checkOperationalRecord kenv.find? originOf
        (fun name => if name == spec.parent then true else flags name)
        spec.origin originalCI originalCI)
    let bridge : ConstantInfo := .defnInfo {
      name := `Gram6AuditNegative.operationalBridge, levelParams := [],
      type := mkConst ``Nat, value := mkConst spec.name [.zero],
      hints := .opaque, safety := .safe }
    let proofOnly : TheoremVal := {
      name := `Gram6AuditNegative.operationalProofBody, levelParams := [],
      type := mkConst ``True, value := mkConst spec.name [.zero] }
    let typeOnly : ConstantInfo := .thmInfo {
      name := `Gram6AuditNegative.operationalTypeOnly, levelParams := [],
      type := mkConst spec.name [.zero], value := mkConst ``True.intro }
    let indirect : ConstantInfo := .thmInfo {
      name := `Gram6AuditNegative.operationalIndirect, levelParams := [],
      type := mkConst ``True, value := mkConst bridge.name }
    let lookup := fun name =>
      if name == bridge.name then some bridge
      else if name == proofOnly.name then some (.thmInfo proofOnly)
      else if name == typeOnly.name then some typeOnly
      else if name == indirect.name then some indirect else kenv.find? name
    for name in [spec.name, bridge.name, proofOnly.name, typeOnly.name, indirect.name] do
      expectRejected s!"recognized operational dependency remains forbidden through {name}"
        "unsafe or partial dependency" (traceDependencies lookup #[name])
    expectRejected s!"{spec.name}: recognized operational dependency in stored proof variant"
      "unsafe or partial dependency" (traceStoredVariant lookup proofOnly)

def enumerateProject (env : Environment) : CoreM ProjectInventory := do
  let kenv := env.checked.get
  let mut modules : NameSet := {}
  let mut names : NameSet := {}
  let mut roots : Array Name := #[]
  let mut variants : Array StoredTheoremVariant := #[]
  let mut records : Nat := 0
  let mut duplicates : Nat := 0
  let mut storedOperational : NameSet := {}
  let mut effectiveOperational : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let origin := env.header.moduleNames[i]!
    if (`PBCounterexample).isPrefixOf origin then
      unless expectedProjectModules.contains origin do
        throwError "Unexpected project module (including higher counterexamples): {origin}"
      modules := modules.insert origin
      let data := env.header.moduleData[i]!
      unless data.constNames.size == data.constants.size do
        throwError "Project module has unequal declaration/name arrays: {origin}"
      logInfo m!"GRAM6_PROJECT_MODULE {origin} records={data.constants.size}"
      for name in data.constNames, stored in data.constants do
        records := records + 1
        let some ci := kenv.find? name
          | throwError "Stored project declaration is missing: {origin} {name}"
        let some idx := env.getModuleIdxFor? name
          | throwError "Project declaration has no defining module: {name}"
        let definingOrigin := env.header.moduleNames[idx.toNat]!
        unless expectedProjectModules.contains definingOrigin do
          throwError "Project record resolves outside the expected closure: {origin} {name}"
        unless stored.name == name do
          throwError "Stored project declaration has a different name: {origin} {name}"
        let operational := ci.isUnsafe || ci.isPartial || stored.isUnsafe ||
          stored.isPartial || (operationalSpec? name).isSome
        if operational then
          let spec ← match checkOperationalRecord kenv.find? (registeredOrigin env)
              (fun n => isNoncomputable env n) origin stored ci with
            | .ok spec => pure spec
            | .error reason => throwError "{reason}: {origin} {name}"
          if storedOperational.contains name then
            throwError "Unexpected duplicate stored operational record: {origin} {name}"
          storedOperational := storedOperational.insert name
          logInfo m!"GRAM6_OPERATIONAL_STORED_RECORD_CHECKED {origin} {name} parent={spec.parent} complete_body_equal=true safety=partial hints=opaque all=[self] levels=[u_1] noncomputable={spec.noncomputableFlag}; not a mathematical root"
          logInfo m!"GRAM6_OPERATIONAL_TYPE {name} {ci.type}"
          logInfo m!"GRAM6_OPERATIONAL_BODY_DEPENDENCIES {name} {(rawDependencies ci).qsort Name.lt}"
        else
          match storedTheoremVariant? stored ci with
          | .error reason => throwError "{reason}: {origin} {name}"
          | .ok none => pure ()
          | .ok (some info) =>
            variants := variants.push { origin := origin, info := info }
            logInfo m!"GRAM6_STORED_PROOF_VARIANT_RETAINED stored={origin} name={name}; raw traversal and fresh-name kernel checking required"
        if idx.toNat != i then
          duplicates := duplicates + 1
          logInfo m!"GRAM6_DUPLICATE_RECORD {name} stored={origin} first_registered={definingOrigin}"
        if names.contains name then continue
        names := names.insert name
        if !operational then
          roots := roots.push name
          logInfo m!"GRAM6_PROJECT_DECL {definingOrigin} {declarationKind ci} {name}"
  for origin in expectedProjectModules do
    unless modules.contains origin do
      throwError "Expected six-dimensional dependency module was omitted: {origin}"
  for (name, ci) in kenv.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if (`PBCounterexample).isPrefixOf origin then
        unless expectedProjectModules.contains origin do
          throwError "Unexpected project origin in kernel inventory: {origin} {name}"
        let operational := ci.isUnsafe || ci.isPartial || (operationalSpec? name).isSome
        if operational then
          match checkOperationalRecord kenv.find? (registeredOrigin env)
              (fun n => isNoncomputable env n) origin ci ci with
          | .error reason => throwError "{reason}: effective {origin} {name}"
          | .ok _ => pure ()
          effectiveOperational := effectiveOperational.insert name
          logInfo m!"GRAM6_OPERATIONAL_EFFECTIVE_RECORD_CHECKED {origin} {name}"
        if !names.contains name then
          names := names.insert name
          if !operational then roots := roots.push name
          logInfo m!"GRAM6_EXTRA_PROJECT_DECL {origin} {declarationKind ci} {name} operational={operational}"
    else if (`PBCounterexample).isPrefixOf name then
      throwError "Project-named declaration has no module origin: {name}"
  for name in finalRoots do
    unless roots.contains name do
      throwError "Required final mathematical root was omitted: {name}"
  for spec in operationalSpecs do
    unless storedOperational.contains spec.name && effectiveOperational.contains spec.name do
      throwError "Expected operational record is absent from stored or effective inventory: {spec.name}"
  unless storedOperational.size == operationalSpecs.size &&
      effectiveOperational.size == operationalSpecs.size &&
      roots.size + effectiveOperational.size == names.size do
    throwError "Project inventory does not account for every mathematical or operational record"
  logInfo m!"GRAM6_PROJECT_INVENTORY_OK modules={modules.size} all_project_names={names.size} safe_roots={roots.size} records={records} duplicates={duplicates} retained_proof_variants={variants.size} stored_operational={storedOperational.size} effective_operational={effectiveOperational.size}"
  return {
    roots := roots
    variants := variants
    operational := effectiveOperational.toArray.qsort Name.lt }

def replayNegativeControl (kenv : Kernel.Environment) : CoreM Unit := do
  let badName := `Gram6AuditNegative.invalidProof
  let bad : ConstantInfo := .thmInfo {
    name := badName
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro }
  let lookup : Name → Option ConstantInfo :=
    fun name => if name == badName then some bad else kenv.find? name
  let .ok dependencies := traceDependencies lookup #[badName]
    | throwError "Could not construct the kernel negative control"
  let rejected : Bool ← Lean.Core.liftIOCore <| do
    let empty ← mkEmptyEnvironment 0
    try
      let _ ← empty.toKernelEnv.replay dependencies.constants
      pure false
    catch ex =>
      unless (toString ex).contains "mismatch" do
        throw <| IO.userError s!"Kernel control failed for an unintended reason: {ex}"
      IO.println s!"GRAM6_KERNEL_NEGATIVE_CONTROL_OK invalid proof rejected: {ex}"
      pure true
  unless rejected do
    throwError "Empty-kernel replay accepted a proof of False with body True.intro"

/-- Add the unchanged type and body under a fresh name through the kernel's
checking API, never through replay's duplicate-theorem optimization. The
caller has already rejected dependencies back to the original name. -/
def kernelCheckStoredVariant (checked : Kernel.Environment)
    (info : TheoremVal) (freshName : Name) : IO Kernel.Environment := do
  unless checked.header.trustLevel == 0 do
    throw <| IO.userError "Stored-variant checker requires trust level zero"
  if (checked.find? freshName).isSome then
    throw <| IO.userError s!"Stored-variant check name already exists: {freshName}"
  let renamed : TheoremVal := {
    info with
    name := freshName
    all := info.all.map (fun name => if name == info.name then freshName else name) }
  let next ← match checked.addDeclCore 0 0 (.thmDecl renamed) (cancelTk? := none) with
    | .ok next => pure next
    | .error ex =>
      throw <| IO.userError (← ex.toMessageData {} |>.toString)
  let some verified := next.find? freshName
    | throw <| IO.userError s!"Kernel omitted the fresh stored-proof check: {freshName}"
  unless sameDeclaration (.thmInfo renamed) verified do
    throw <| IO.userError s!"Kernel changed stored-proof check information: {freshName}"
  return next

/-- A valid effective theorem must not cause an invalid alternate body to be
accepted or skipped. The alternate body uses the actual variant pathway. -/
def storedVariantKernelNegativeControl (kenv : Kernel.Environment) : CoreM Unit := do
  let original : TheoremVal := {
    name := `Gram6AuditNegative.effectiveDuplicate
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro }
  let bad : TheoremVal := { original with value := mkConst ``Nat.zero }
  let .ok (some retained) := storedTheoremVariant? (.thmInfo bad) (.thmInfo original)
    | throwError "Invalid alternate-body control was not retained for checking"
  let lookup : Name → Option ConstantInfo :=
    fun name => if name == original.name then some (.thmInfo original) else kenv.find? name
  let .ok originalTrace := traceDependencies lookup #[original.name]
    | throwError "Could not construct the effective duplicate control"
  let .ok alternateTrace := traceStoredVariant lookup retained
    | throwError "Could not traverse the invalid alternate-body control"
  let mut constants := originalTrace.constants
  for (name, ci) in alternateTrace.constants.toList do
    if name == original.name then continue
    if let some previous := constants[name]? then
      unless sameDeclaration previous ci do
        throwError "Control dependency merge changed a declaration: {name}"
    constants := constants.insert name ci
  let rejected : Bool ← Lean.Core.liftIOCore do
    let empty ← mkEmptyEnvironment 0
    let checked ← empty.toKernelEnv.replay constants
    let some effective := checked.find? original.name
      | throw <| IO.userError "Valid effective duplicate control was not replayed"
    unless sameDeclaration (.thmInfo original) effective do
      throw <| IO.userError "Valid effective duplicate control was changed"
    try
      let _ ← kernelCheckStoredVariant checked retained
        `Gram6AuditNegative.freshInvalidDuplicate
      pure false
    catch ex =>
      unless (toString ex).contains "mismatch" do
        throw <| IO.userError s!"Alternate-body control failed for an unintended reason: {ex}"
      IO.println s!"GRAM6_KERNEL_NEGATIVE_CONTROL_OK invalid alternate stored body rejected: {ex}"
      pure true
  unless rejected do
    throwError "Kernel accepted an invalid alternate proof after a valid same-name theorem"

def runAudit (withReplay : Bool) : CoreM Unit := do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  unless env.header.trustLevel == 0 do
    throwError "Audit imported with a nonzero kernel trust level"
  auditStage "trust-zero entry"
  negativeControls kenv
  operationalNegativeControls env
  auditStage "initial negative controls complete"
  let inventory ← enumerateProject env
  let roots := inventory.roots
  auditStage s!"project inventory complete; roots={roots.size}; stored_variants={inventory.variants.size}"
  let result ← match traceDependencies kenv.find? roots with
    | .ok result => pure result
    | .error reason => throwError "{reason}"
  auditStage s!"effective raw dependency traversal complete; constants={result.constants.size}"
  let mut replayConstants := result.constants
  let mut allAxioms := result.axioms
  for variant in inventory.variants do
    let alternate ← match traceStoredVariant kenv.find? variant.info with
      | .ok alternate => pure alternate
      | .error reason => throwError "{reason}: stored in {variant.origin}"
    unless result.constants.contains variant.info.name do
      throwError "Stored proof variant lacks an audited effective root: {variant.info.name}"
    for (name, ci) in alternate.constants.toList do
      -- This one body is retained in inventory.variants, not discarded. The map
      -- retains the effective body; the alternate is separately kernel-checked.
      if name == variant.info.name then continue
      if let some previous := replayConstants[name]? then
        unless sameDeclaration previous ci do
          throwError "Stored-variant dependency differs from effective dependency: {name}"
      replayConstants := replayConstants.insert name ci
    for ax in alternate.axioms do allAxioms := allAxioms.insert ax
    logInfo m!"GRAM6_STORED_PROOF_VARIANT_RAW_OK stored={variant.origin} name={variant.info.name} constants={alternate.constants.size} axioms={alternate.axioms.toArray.qsort Name.lt}; kernel check pending"
  auditStage s!"all stored variant raw traversals complete; combined_constants={replayConstants.size}"
  for name in inventory.operational do
    if replayConstants.contains name then
      throwError "Operational implementation is reachable from a safe root or stored proof: {name}"
    logInfo m!"GRAM6_OPERATIONAL_UNREACHABLE_FROM_ALL_SAFE_ROOTS_AND_VARIANTS {name}"
  let rawAxioms := result.axioms.toArray.qsort Name.lt
  let allRawAxioms := allAxioms.toArray.qsort Name.lt
  let mut reportedAxioms : NameSet := {}
  for name in roots do
    let reported ← collectAxioms name
    for ax in reported do reportedAxioms := reportedAxioms.insert ax
    logInfo m!"GRAM6_CACHED_AXIOMS {name} {reported}"
  unless rawAxioms == reportedAxioms.toArray.qsort Name.lt do
    throwError "Raw dependencies disagree with cached axiom data"
  for ax in allRawAxioms do
    let some idx := env.getModuleIdxFor? ax
      | throwError "Allowed axiom has no standard defining module: {ax}"
    let actualOrigin := env.header.moduleNames[idx.toNat]!
    unless standardAxiomOrigin ax == some actualOrigin do
      throwError "Allowed axiom has a nonstandard origin: {ax} {actualOrigin}"
    let some ci := kenv.find? ax | throwError "Allowed axiom is missing: {ax}"
    logInfo m!"GRAM6_STANDARD_AXIOM_SCHEMA_OK {ax} origin={actualOrigin} TYPE {ci.type}"
  logInfo m!"GRAM6_INDEPENDENT_RAW_AUDIT_OK roots={roots.size} effective_constants={result.constants.size} combined_constants={replayConstants.size} definitions={result.definitions} theorems={result.theorems} stored_proof_variants={inventory.variants.size} axioms={allRawAxioms}"
  for name in finalRoots do
    let some ci := kenv.find? name | throwError "Missing final declaration {name}"
    logInfo m!"GRAM6_FINAL_TYPE {name} {ci.type}"
  if withReplay then
    replayNegativeControl kenv
    storedVariantKernelNegativeControl kenv
    auditStage "both kernel negative controls complete"
    let empty ← Lean.Core.liftIOCore <| mkEmptyEnvironment 0
    unless empty.header.trustLevel == 0 && empty.header.moduleNames.isEmpty &&
        empty.toKernelEnv.constants.toList.isEmpty do
      throwError "The replay starting environment is not empty at trust level zero"
    auditStage "empty trust-zero kernel replay begins"
    let mut checked ← Lean.Core.liftIOCore <| empty.toKernelEnv.replay replayConstants
    for (name, original) in replayConstants.toList do
      let some verified := checked.find? name
        | throwError "Kernel replay omitted a mathematical dependency: {name}"
      unless sameDeclaration original verified do
        throwError "Kernel replay changed declaration information: {name}"
    for name in roots do
      unless (checked.find? name).isSome do
        throwError "Kernel replay omitted a project root: {name}"
    for name in inventory.operational do
      if (checked.find? name).isSome then
        throwError "Kernel replay unexpectedly contains an operational implementation: {name}"
    auditStage "effective closure and all additional stored-proof dependencies replayed"
    let mut variantIndex : Nat := 0
    for variant in inventory.variants do
      let freshName := Name.mkNum `Gram6IndependentStoredProof.checked variantIndex
      if (kenv.find? freshName).isSome then
        throwError "Stored-proof check name collides with an imported declaration: {freshName}"
      auditStage s!"stored proof kernel check begins: {variant.origin} {variant.info.name}"
      checked ← Lean.Core.liftIOCore <| kernelCheckStoredVariant checked variant.info freshName
      logInfo m!"GRAM6_STORED_PROOF_VARIANT_KERNEL_OK stored={variant.origin} original={variant.info.name} fresh_check={freshName}"
      variantIndex := variantIndex + 1
    auditStage "every retained stored proof body kernel-checked"
    logInfo m!"GRAM6_INDEPENDENT_EMPTY_KERNEL_REPLAY_OK roots={roots.size} supplied_constants={replayConstants.size} stored_proof_variants={inventory.variants.size} axioms={allRawAxioms}"

end Gram6IndependentAudit

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftCoreM (Gram6IndependentAudit.runAudit true)

import PBCounterexample.SymmetricMain
import PBCounterexample.Collaborator30Main
import Lean

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

run_cmd checkStandardFoundationTypes30

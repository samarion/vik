import Lean
import Vik
open Lean Elab Command

/-- Fails unless every theorem of `Vik` uses only Lean's standard axioms. -/
elab "#check_vik_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.map₁.toList do
    if !((`Vik).isPrefixOf name) || name.isInternal then continue
    match info with
    | .thmInfo _ =>
      count := count + 1
      let axioms ← liftCoreM (collectAxioms name)
      for a in axioms do
        if !allowed.contains a then
          throwError m!"{name} depends on {a}"
    | _ => pure ()
  logInfo m!"{count} theorems, all on Lean's standard axioms"

#check_vik_axioms

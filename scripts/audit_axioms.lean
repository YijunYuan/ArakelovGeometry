import ArakelovGeometry
import Lean

/-!
# Transitive project axiom inventory

Run after `lake build`, using `lake env lean scripts/audit_axioms.lean`.
Every constant whose defining module belongs to this project is inspected,
including generated declarations and names outside the project namespace.
`GAP` lines identify transitive dependencies on `sorryAx`; the summary is an
inventory, not a claim that the project is complete. Other nonstandard axioms
are reported as errors.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut tainted : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`ArakelovGeometry).isPrefixOf env.header.moduleNames[idx.toNat]! then
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        if axioms.contains ``sorryAx then
          tainted := tainted + 1
          logInfo m!"GAP {name}"
        for ax in axioms do
          unless [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains ax do
            logError m!"NONSTANDARD {name}: {ax}"
  logInfo m!"AUDIT checked={checked} sorryAx={tainted}"

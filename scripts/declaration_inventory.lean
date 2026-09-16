import ArakelovGeometry
import Lean

/-!
# Compiled declaration inventory

Run after the configured build with
`horizon check --lean scripts/declaration_inventory.lean`.
The JSON records every project constant (including generated declarations),
its direct constant dependencies and its transitive axioms. Dependencies in
external libraries remain references; they are not project blueprint nodes.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`ArakelovGeometry).isPrefixOf mod then
        let axioms ← Lean.collectAxioms name
        let ranges ← findDeclarationRanges? name
        let deps := (info.type.getUsedConstants ++
          ((info.value? true).map Expr.getUsedConstants).getD #[]).toList.eraseDups
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson mod.toString),
          ("line", toJson (ranges.map fun r ↦ r.range.pos.line)),
          ("end_line", toJson (ranges.map fun r ↦ r.range.endPos.line)),
          ("dependencies", toJson (deps.map Name.toString)),
          ("axioms", toJson (axioms.toList.map Name.toString))]
  rows := rows.qsort fun a b ↦
    (a.getObjValAs? String "name").toOption.getD "" <
      (b.getObjValAs? String "name").toOption.getD ""
  IO.FS.writeFile "docs/declaration-inventory.json" ((toJson rows).pretty ++ "\n")
  logInfo m!"INVENTORY project_constants={rows.size}"

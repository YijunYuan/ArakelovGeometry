import ArakelovGeometry
import Lean

/-!
# Imported blueprint boundaries

Check the exact external producers recorded in `docs/imported-boundaries.json`.
They remain library references, never project graph nodes. Their transitive
axioms must belong to the same standard set allowed for project declarations.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let catalog ← IO.FS.readFile "docs/imported-boundaries.json"
  let json ← ofExcept (Json.parse catalog)
  let object ← ofExcept json.getObj?
  let mut rows : Array Json := #[]
  for (label, entry) in object.toList do
    let names ← ofExcept (entry.getObjValAs? (Array String) "producers")
    for str in names do
      let name := str.toName
      unless env.contains name do throwError "Unknown imported producer {str}"
      let some idx := env.getModuleIdxFor? name
        | throwError "Imported producer has no module: {str}"
      let mod := env.header.moduleNames[idx.toNat]!
      if (`ArakelovGeometry).isPrefixOf mod then
        throwError "Project producer classified as imported: {str}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard imported axiom {label}: {str}: {ax}"
      rows := rows.push <| Json.mkObj [
        ("node", toJson label), ("name", toJson str),
        ("module", toJson mod.toString),
        ("axioms", toJson (axioms.toList.map Name.toString))]
  IO.FS.writeFile "docs/imported-boundary-audit.json" ((toJson rows).pretty ++ "\n")
  logInfo m!"IMPORTED boundaries={object.size} producers={rows.size}"

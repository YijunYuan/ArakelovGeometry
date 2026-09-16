#!/usr/bin/env python3
"""Audit project-only kernel inventory against the authored mathematical route.

Run declaration_inventory.lean after the build, then run this from the project
root. No dependency source tree or generated graph is scanned. An absent
attachment is reported explicitly, never treated as mathematical completion.
"""

import argparse
import hashlib
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Anonymous instances and private proof support have kernel names that need an
# explicit mathematical owner. These mappings do not claim a separate theorem
# attachment; their axioms and compiled dependency paths remain audited.
IMPLEMENTATION_OWNER_NODES = {
    "_private.ArakelovGeometry.AdelicCurve.Extension.0.ArakelovGeometry.AdelicStructure."
    "ParameterSpaceFinExtension.isScalarTower_completion_separableClosure":
        "lem:completion-separable-closure",
    "ArakelovGeometry.AdelicCurve.instIsProperTrivialAdelicCurve":
        "prop:proper-trivial-adelic-curve",
    "ArakelovGeometry.AdelicCurve.instIsProperNumberFieldAdelicCurve":
        "cor:number-field-proper",
    "ArakelovGeometry.AdelicCurve.instIsProperFunctionFieldAdelicCurve":
        "thm:ff-integral-product-formula",
}

# These congruence lemmas are generated in project modules for imported
# operations. They express substitutivity, not new library declarations or
# independently authored mathematical theorems. Keep them in the axiom audit
# and map them to the project construction using the underlying operation.
GENERATED_SUPPORT = {
    "CauSeq.IsComplete.congr_simp": "CauSeq.isComplete_completion",
    "IsDedekindDomain.HeightOneSpectrum.adicAbv.congr_simp":
        "ArakelovGeometry.AdelicStructure.pointAbv",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory_provenance(paths, record):
    """Bind the compiled inventory to sources, artifacts and successful checks.

    Recording requires the configured build followed by the inventory check.
    Subsequent coverage runs reject changed sources or inventory. This records
    evidence from the checks; it does not replace kernel verification.
    """
    manifest = ROOT / "docs/inventory-provenance.json"
    current = {str(p.relative_to(ROOT)): sha256(p) for p in paths}
    current["scripts/declaration_inventory.lean"] = sha256(ROOT / "scripts/declaration_inventory.lean")
    current["docs/declaration-inventory.json"] = sha256(ROOT / "docs/declaration-inventory.json")
    if record:
        session = Path(os.environ["ARCHON_HORIZON_SESSION_DIR"])
        checks = [json.loads(p.read_text()) for p in (session / "checks").glob("*.json")]
        builds = [c for c in checks if c.get("ok") and c.get("command") == ["lake", "build"]]
        inventories = [c for c in checks if c.get("ok") and
                       c.get("command", [""])[-1].endswith("scripts/declaration_inventory.lean")]
        if not builds or not inventories:
            raise ValueError("Record provenance only after a configured build and inventory check")
        build = max(builds, key=lambda c: c["finished_epoch"])
        inventory = max(inventories, key=lambda c: c["finished_epoch"])
        if inventory["finished_epoch"] < build["finished_epoch"]:
            raise ValueError("Inventory check predates configured build")
        if any(p.stat().st_mtime > build["finished_epoch"] for p in paths):
            raise ValueError("Project sources changed after the configured build")
        artifacts = {}
        for p in paths:
            artifact = ROOT / ".lake/build/lib/lean" / p.relative_to(ROOT).with_suffix(".olean")
            if not artifact.exists() or artifact.stat().st_mtime < p.stat().st_mtime:
                raise ValueError(f"Missing or outdated compiled artifact: {artifact}")
            if artifact.stat().st_mtime > inventory["finished_epoch"]:
                raise ValueError(f"Compiled artifact postdates inventory: {artifact}")
            artifacts[str(artifact.relative_to(ROOT))] = sha256(artifact)
        evidence = {"sources_and_inventory_sha256": current,
                    "compiled_artifacts_sha256": artifacts,
                    "build": build, "inventory_check": inventory}
        manifest.write_text(json.dumps(evidence, indent=2) + "\n")
    if not manifest.exists():
        return ["Missing inventory provenance; run --record-provenance after the required checks"]
    evidence = json.loads(manifest.read_text())
    saved = evidence["sources_and_inventory_sha256"]
    return [p for p in sorted(current.keys() | saved.keys()) if current.get(p) != saved.get(p)]


def included_blueprints():
    """Read only the live route rooted at content.tex, not dormant drafts."""
    pending = [ROOT / "blueprint/src/content.tex"]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        source = re.sub(r"(?m)%.*$", "", path.read_text())
        for name in re.findall(r"\\input\{([^}]+)\}", source):
            child = path.parent / name
            pending.append(child if child.suffix else child.with_suffix(".tex"))
    return sorted(seen)


def lean_code(text):
    """Blank comments and strings while preserving offsets and line numbers."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text[i:i + 2] == "/-":
                depth += 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if text[i:i + 2] == "-/":
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
                continue
        elif string:
            if text[i] == "\\":
                out[i:i + 2] = "  "
                i += 2
                continue
            if text[i] == '"':
                string = False
        elif text[i:i + 2] == "/-":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
            continue
        elif text[i] == '"':
            string = True
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def blueprint_nodes():
    nodes, attached = {}, {}
    for path in included_blueprints():
        text = re.sub(r"(?m)%.*$", "", path.read_text())
        for match in re.finditer(
            r"\\begin\{(definition|lemma|theorem|proposition|corollary|remark|notation)\}"
            r"(.*?)\\end\{\1\}", text, re.S
        ):
            body = match[2]
            label = re.search(r"\\label\{([^}]+)\}", body)
            if not label:
                continue
            label = label[1]
            if label in nodes:
                raise ValueError(f"duplicate blueprint label: {label}")
            uses = [s.strip() for x in re.findall(r"\\uses\{([^}]+)\}", body)
                    for s in x.split(",") if s.strip()]
            names = [s.strip() for x in re.findall(r"\\lean\{([^}]+)\}", body)
                     for s in x.split(",") if s.strip()]
            anchors = [s.strip() for x in re.findall(r"\\source\{([^}]+)\}", body)
                       for s in x.split(",") if s.strip()]
            nodes[label] = {"file": str(path.relative_to(ROOT)), "uses": uses,
                            "lean": names, "sources": anchors,
                            "leanok": r"\leanok" in body,
                            "notready": r"\notready" in body}
            for name in names:
                attached.setdefault(name, []).append(label)
    return nodes, attached


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--record-provenance", action="store_true")
    args = parser.parse_args()
    rows = json.loads((ROOT / "docs/declaration-inventory.json").read_text())
    by_name = {r["name"]: r for r in rows}
    nodes, attached = blueprint_nodes()
    sources = {}
    for path in sorted((ROOT / "ArakelovGeometry").rglob("*.lean")) + [ROOT / "ArakelovGeometry.lean"]:
        sources[str(path.relative_to(ROOT)).replace("/", ".")[:-5]] = (
            path, lean_code(path.read_text()))
    stale_inventory = inventory_provenance([p for p, _ in sources.values()], args.record_provenance)
    # A namespace prefix is not an attachment: e.g. mapping AdelicStructure
    # must never silently map every theorem in its namespace. Determine the
    # nearest *authored declaration*, then inherit only for its generated
    # fields, recursors, equations and auxiliary constants.
    authored = set()
    for row in rows:
        if row["line"] is None:
            continue
        code = sources[row["module"]][1].splitlines()
        fragment = "\n".join(code[row["line"] - 1:row["end_line"]])
        decl = re.search(r"\b(theorem|lemma|def|abbrev|structure|class|inductive|instance)\b"
                         r"\s*([^\s:(\[{]+)?", fragment)
        if not decl:
            continue
        stated = (decl[2] or "").removeprefix("_root_.")
        if ((decl[1] == "instance" and not stated)
                or row["name"] == stated or row["name"].endswith("." + stated)):
            authored.add(row["name"])
    gaps = []
    for mod, (path, code) in sources.items():
        for match in re.finditer(r"\b(sorry|admit)\b", code):
            line = code.count("\n", 0, match.start()) + 1
            owners = [r for r in rows if r["name"] in authored and r["module"] == mod and r["line"]
                      and r["line"] <= line <= r["end_line"]]
            # Generated proof constants share the enclosing source range;
            # retain the shortest enclosing declaration name as its owner.
            owners.sort(key=lambda r: (r["end_line"] - r["line"], len(r["name"])))
            owner = owners[0]["name"] if owners else None
            gaps.append({"file": str(path.relative_to(ROOT)), "line": line,
                         "token": match[1], "declaration": owner,
                         "nodes": attached.get(owner, [])})
    target = [r for r in rows if r["module"] == "ArakelovGeometry.AdelicCurve.Extension"]
    for row in rows:
        name = row["name"]
        candidates = [n for n in authored if name == n or name.startswith(n + ".")]
        parent = max(candidates, key=len) if candidates else None
        row["authored_declaration"] = parent
        row["blueprint_nodes"] = attached.get(name, attached.get(parent, []))
        row["attachment"] = name if name in attached else parent if parent in attached else None
        if name in IMPLEMENTATION_OWNER_NODES:
            label = IMPLEMENTATION_OWNER_NODES[name]
            row["implementation_owner"] = label
            row["blueprint_nodes"] = [label] if label in nodes else []
            if label in nodes:
                nodes[label].setdefault("implementation_support", []).append(name)
        if name in GENERATED_SUPPORT:
            if row["line"] is not None or not name.endswith(".congr_simp"):
                raise ValueError(f"Expected an unlocated generated congruence lemma: {name}")
            row["generated_support_for"] = GENERATED_SUPPORT[name]
            row["blueprint_nodes"] = attached.get(GENERATED_SUPPORT[name], [])
        row["project_dependencies"] = [d for d in row["dependencies"] if d in by_name]
        row["external_dependencies"] = [d for d in row["dependencies"] if d not in by_name]
    missing = [r["name"] for r in target if not r["blueprint_nodes"]]
    unknown = sorted(set(attached) - set(by_name))
    dangling = [(n, d) for n, v in nodes.items() for d in v["uses"] if d not in nodes]
    missing_sources = []
    for label, node in nodes.items():
        for anchor in node["sources"]:
            slug, _, page = anchor.partition(":")
            path = ROOT.parent / "references" / slug
            if page:
                path = path / "tex" / (page + ".tex")
            if not path.exists():
                missing_sources.append((label, anchor))
    cycles, visiting, visited = [], set(), set()

    def visit(node, trail):
        if node in visiting:
            cycles.append(trail[trail.index(node):] + [node])
            return
        if node in visited or node not in nodes:
            return
        visiting.add(node)
        for dep in nodes[node]["uses"]:
            visit(dep, trail + [node])
        visiting.remove(node)
        visited.add(node)

    for node in nodes:
        visit(node, [])
    false_completion = [label for label, node in nodes.items()
                        if node["leanok"] and (node["notready"] or not node["lean"]
                        or any(name not in by_name or "sorryAx" in by_name[name]["axioms"]
                               for name in node["lean"]))]
    # Ancillary project constants are recorded as support of the actual
    # consuming statements; this is distinct from a formalizes attachment.
    for label, node in nodes.items():
        todo, seen = list(node["lean"]), set()
        while todo:
            name = todo.pop()
            if name in seen or name not in by_name:
                continue
            seen.add(name)
            row = by_name[name]
            row.setdefault("supports_nodes", []).append(label)
            todo.extend(row["project_dependencies"])
    unmapped_project = [r["name"] for r in rows
                        if not r["blueprint_nodes"] and not r.get("supports_nodes")]
    for row in rows:
        row["coverage_kind"] = ("attachment" if row["attachment"] else
                                "instance_owner" if row.get("implementation_owner") and row["blueprint_nodes"] else
                                "generated_congruence" if row.get("generated_support_for") and row["blueprint_nodes"] else
                                "dependency_support" if row.get("supports_nodes") else "unmapped")

    def reachable(label):
        todo, seen = [label], set()
        while todo:
            node = todo.pop()
            if node in seen or node not in nodes:
                continue
            seen.add(node)
            todo.extend(nodes[node]["uses"])
        return seen

    reach = {label: reachable(label) for label in nodes}
    missing_routes, elaboration_dependencies = [], []
    for row in rows:
        if row["name"] not in attached:
            continue
        for dep in row["project_dependencies"]:
            target_nodes = by_name[dep]["blueprint_nodes"]
            if not target_nodes:
                continue
            witness = {"declaration": row["name"], "dependency": dep,
                       "from_nodes": attached[row["name"]], "to_nodes": target_nodes}
            if any(t in reach[s] for s in witness["from_nodes"] for t in target_nodes):
                continue
            if "._proof_" in dep:
                # Lean shares generated instance proof terms across declarations.
                # Keep those edges visible, but they are not mathematical uses.
                witness["reason"] = "shared generated proof term; retained as elaboration dependency"
                elaboration_dependencies.append(witness)
            else:
                missing_routes.append(witness)
    nonstandard = [(r["name"], a) for r in rows for a in r["axioms"]
                   if a not in {"propext", "Classical.choice", "Quot.sound", "sorryAx"}]
    result = {"summary": {"project_constants": len(rows), "target_constants": len(target),
              "direct_gaps": len(gaps), "sorry_backed_constants": sum("sorryAx" in r["axioms"] for r in rows),
              "blueprint_nodes": len(nodes), "unmapped_target_constants": len(missing),
              "unmapped_direct_gaps": sum(not g["nodes"] for g in gaps),
              "required_project_support_constants": sum(bool(r.get("supports_nodes")) for r in rows),
              "unmapped_project_constants": len(unmapped_project),
              "missing_compiled_dependency_routes": len(missing_routes),
              "stale_inventory_files": len(stale_inventory),
              "unwritten_mathematical_nodes": sum(n["notready"] for n in nodes.values()),
              "nodes_without_lean_attachments": sum(not n["lean"] and not k.startswith("rem:")
                                                    for k, n in nodes.items()),
              "dependency_cycles": len(cycles), "false_completion_markers": len(false_completion)},
              "direct_gaps": gaps, "nodes": nodes, "declarations": rows,
              "unmapped_target": missing, "unknown_attachments": unknown,
              "dangling_dependencies": dangling, "nonstandard_axioms": nonstandard,
              "missing_sources": missing_sources, "dependency_cycles": cycles,
              "false_completion_markers": false_completion,
              "unmapped_project": unmapped_project, "stale_inventory": stale_inventory,
              "missing_compiled_dependency_routes": missing_routes,
              "elaboration_dependencies": elaboration_dependencies}
    (ROOT / "docs/blueprint-coverage.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    lines = ["# Complete extension obligation inventory", "",
             "Generated by `scripts/blueprint_coverage.py` from the compiled project inventory.",
             "Every project constant, including generated declarations, and every direct dependency",
             "is recorded in `blueprint-coverage.json`. External constants remain library references.",
             "A mapped obligation is still open until its transitive axiom audit is clean.", "",
             f"Project constants: {len(rows)}; extension constants: {len(target)}; direct gaps: {len(gaps)}.",
             f"Sorry-backed constants: {result['summary']['sorry_backed_constants']}; blueprint nodes: {len(nodes)}.",
             f"Unmapped extension constants: {len(missing)}; unmapped gaps: {result['summary']['unmapped_direct_gaps']}.", "",
             f"Unmapped project constants: {len(unmapped_project)}; missing compiled dependency routes: {len(missing_routes)}.",
             f"Unwritten mathematical blueprint nodes: {result['summary']['unwritten_mathematical_nodes']}.",
             f"Changed or unrecorded inventory inputs: {len(stale_inventory)}.", "",
             "| Gap | Source line | Declaration | Blueprint nodes |", "| --- | --- | --- | --- |"]
    for i, gap in enumerate(gaps, 1):
        labels = ", ".join(gap["nodes"]) or "UNMAPPED"
        lines.append(f"| {i} | {gap['line']} | `{gap['declaration']}` | {labels} |")
    lines += ["", "All gap source lines are in `ArakelovGeometry/AdelicCurve/Extension.lean`.",
              "The machine-readable inventory also retains the prior chapters and examples,",
              "whose constants are mapped by exact attachments, explicit anonymous-instance owners,",
              "or actual compiled dependency paths to consuming blueprint nodes. A support mapping",
              "is not a formalizes attachment. Completeness checks every project constant.", ""]
    (ROOT / "docs/obligations.md").write_text("\n".join(lines))
    print(json.dumps(result["summary"], indent=2))
    if args.require_complete and (missing or unknown or dangling or nonstandard
                                 or missing_sources or cycles or false_completion or unmapped_project
                                 or stale_inventory or missing_routes
                                 or any(not g["nodes"] for g in gaps)):
        raise SystemExit("Incomplete blueprint coverage; see docs/blueprint-coverage.json")


if __name__ == "__main__":
    main()

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
    "ArakelovGeometry.AdelicCurve.instIsProperTrivialAdelicCurve":
        "prop:proper-trivial-adelic-curve",
    "ArakelovGeometry.AdelicCurve.instIsProperNumberFieldAdelicCurve":
        "cor:number-field-proper",
    "ArakelovGeometry.AdelicCurve.instIsProperFunctionFieldAdelicCurve":
        "thm:ff-integral-product-formula",
}

# These congruence and equation lemmas are generated in project modules for
# imported operations. They express computation, not new library declarations or
# independently authored mathematical theorems. Keep them in the axiom audit
# and map them to the project construction using the underlying operation.
GENERATED_SUPPORT = {
    "Equiv.subtypeEquiv.eq_1": "ArakelovGeometry.prod_initial_comp_perm_eq_iSup_prod",
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
    stale = [p for p in sorted(current.keys() | saved.keys()) if current.get(p) != saved.get(p)]
    for name, digest in evidence.get("compiled_artifacts_sha256", {}).items():
        artifact = ROOT / name
        if not artifact.exists() or sha256(artifact) != digest:
            stale.append(name)
    return stale


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


def imported_boundary_provenance(record, audited):
    """Bind imported producer evidence to its check and exact library inputs."""
    manifest = ROOT / "docs/imported-boundary-provenance.json"
    paths = [ROOT / p for p in (
        "docs/imported-boundaries.json", "docs/imported-boundary-audit.json",
        "scripts/audit_imported_boundaries.lean", "lake-manifest.json",
        "lean-toolchain", ".lake/build/lib/lean/ArakelovGeometry.olean")]
    for mod in sorted({r["module"] for r in audited}):
        paths.append(ROOT / ".lake/packages/mathlib/.lake/build/lib/lean" /
                     (mod.replace(".", "/") + ".olean"))
    absent = [str(p.relative_to(ROOT)) for p in paths if not p.exists()]
    if absent:
        return ["Missing imported audit input: " + p for p in absent]
    current = {str(p.relative_to(ROOT)): sha256(p) for p in paths}
    if record:
        session = Path(os.environ["ARCHON_HORIZON_SESSION_DIR"])
        checks = [json.loads(p.read_text()) for p in (session / "checks").glob("*.json")]
        builds = [c for c in checks if c.get("ok") and c.get("command") == ["lake", "build"]]
        audits = [c for c in checks if c.get("ok") and
                  c.get("command", [""])[-1].endswith("scripts/audit_imported_boundaries.lean")]
        if not builds or not audits:
            return ["Record imported provenance after a configured build and imported audit"]
        build = max(builds, key=lambda c: c["finished_epoch"])
        audit = max(audits, key=lambda c: c["finished_epoch"])
        if audit["finished_epoch"] < build["finished_epoch"]:
            return ["Imported audit predates configured build"]
        if any(p.stat().st_mtime > audit["finished_epoch"] for p in paths):
            return ["Imported audit inputs changed after the recorded audit"]
        manifest.write_text(json.dumps({"inputs_sha256": current,
                                        "build": build, "audit": audit}, indent=2) + "\n")
    if not manifest.exists():
        return ["Missing imported audit provenance"]
    evidence = json.loads(manifest.read_text())
    saved = evidence["inputs_sha256"]
    return ["Stale imported audit input: " + p for p in sorted(current.keys() | saved.keys())
            if current.get(p) != saved.get(p)]


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
            library_refs = [s.strip() for x in re.findall(r"\\dcref\{([^}]+)\}", body)
                            for s in x.split(",") if s.strip()]
            nodes[label] = {"file": str(path.relative_to(ROOT)), "uses": uses,
                            "lean": names, "sources": anchors,
                            "library_references": library_refs,
                            "leanok": r"\leanok" in body,
                            "mathlibok": r"\mathlibok" in body,
                            "notready": r"\notready" in body}
            for name in names:
                attached.setdefault(name, []).append(label)
    return nodes, attached


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--require-closed", action="store_true",
                        help="also reject proof gaps and uncovered mathematical nodes")
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
    target_modules = {
        "ArakelovGeometry.AdelicCurve.Extension",
        "ArakelovGeometry.AdelicCurve.FiniteTower",
        "ArakelovGeometry.AdelicCurve.FiniteProbability",
        "ArakelovGeometry.AdelicCurve.AlgebraicTower",
        "ArakelovGeometry.AdelicCurve.AlgebraicTowerBasic",
        "ArakelovGeometry.AdelicCurve.AlgebraicTowerCylinder",
        "ArakelovGeometry.AdelicCurve.AlgebraicTowerIntegral",
        "ArakelovGeometry.AdelicCurve.AlgebraicIntegrable",
        "ArakelovGeometry.AdelicCurve.AlgebraicCylinder",
        "ArakelovGeometry.AdelicCurve.AlgebraicInverseLimit",
        "ArakelovGeometry.AdelicCurve.BoundedEvaluationGenerators",
        "ArakelovGeometry.ExternalResults.AbsoluteValueTensor",
        "ArakelovGeometry.ExternalResults.BoundedFunctionalMonotoneClass",
        "ArakelovGeometry.ExternalResults.AlgebraicTowerSupport",
        "ArakelovGeometry.AdelicCurve.AlgebraicProbability",
        "ArakelovGeometry.AdelicCurve.AlgebraicFiniteProjection",
        "ArakelovGeometry.AdelicCurve.AlgebraicBaseChange",
    }
    target = [r for r in rows if r["module"] in target_modules]
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
            if row["line"] is not None or not (
                name.endswith(".congr_simp") or re.search(r"\.eq_\d+$", name)
            ):
                raise ValueError(f"Expected an unlocated generated support lemma: {name}")
            row["generated_support_for"] = GENERATED_SUPPORT[name]
            row["blueprint_nodes"] = attached.get(GENERATED_SUPPORT[name], [])
        row["project_dependencies"] = [d for d in row["dependencies"] if d in by_name]
        row["external_dependencies"] = [d for d in row["dependencies"] if d not in by_name]
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
                                "generated_support" if row.get("generated_support_for") and row["blueprint_nodes"] else
                                "dependency_support" if row.get("supports_nodes") else "unmapped")
    # Private proof helpers and compiler-generated subordinate constants may
    # be mapped through their actual compiled consumer cone. This is support,
    # never a formalizes attachment. Public authored target declarations still
    # require their own mathematical mapping, and absent support paths fail.
    def private_or_generated(row):
        return (row["name"].startswith("_private.") or
                bool(row["authored_declaration"] and
                     row["authored_declaration"] != row["name"]) or
                row["name"] in GENERATED_SUPPORT)

    missing = [r["name"] for r in target if not r["blueprint_nodes"] and
               not (private_or_generated(r) and r.get("supports_nodes"))]

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
    # Imported theorems remain external references. A source node needs an
    # explicit, kernel-audited boundary and actual project consumers.
    boundary_path = ROOT / "docs/imported-boundaries.json"
    audit_path = ROOT / "docs/imported-boundary-audit.json"
    boundaries = json.loads(boundary_path.read_text()) if boundary_path.exists() else {}
    false_completion.extend(label for label, node in nodes.items()
                            if node["mathlibok"] and
                            (label not in boundaries or node["lean"] or node["leanok"]))
    audited = json.loads(audit_path.read_text()) if audit_path.exists() else []
    checked = {(r["node"], r["name"]): r for r in audited}
    boundary_errors = imported_boundary_provenance(args.record_provenance, audited) if boundaries else []
    for label, boundary in boundaries.items():
        node = nodes.get(label)
        if node is None:
            boundary_errors.append([label, "unknown blueprint node"])
            continue
        if node["lean"] or node["leanok"] or node["notready"]:
            boundary_errors.append([label, "imported boundary has project or unproved status"])
        producers = set(boundary["producers"])
        if not producers or not producers <= set(node["library_references"]):
            boundary_errors.append([label, "missing exact library references"])
        for name in producers:
            evidence = checked.get((label, name))
            if (not evidence or name in by_name or
                    evidence.get("module", "").startswith("ArakelovGeometry") or
                    any(a not in {"propext", "Classical.choice", "Quot.sound"}
                        for a in evidence.get("axioms", []))):
                boundary_errors.append([label, name, "missing or invalid imported axiom audit"])
        uses = {}
        for consumer in boundary["consumers"]:
            if consumer not in by_name:
                boundary_errors.append([label, consumer, "unknown project consumer"])
                continue
            todo, seen, external = [consumer], set(), set()
            while todo:
                name = todo.pop()
                if name in seen:
                    continue
                seen.add(name)
                row = by_name[name]
                external.update(row["external_dependencies"])
                todo.extend(row["project_dependencies"])
            uses[consumer] = sorted(producers & external)
        if not any(uses.values()):
            boundary_errors.append([label, "no compiled route to any imported producer"])
        boundary["compiled_consumer_uses"] = uses
    unsupported_nodes = [label for label, node in nodes.items()
                         if not label.startswith("rem:") and not node["lean"]
                         and label not in boundaries]
    source_index = json.loads((ROOT / "docs/source-result-index.json").read_text())
    expected_results = ({"3.3.setup", "3.4.setup"} |
                        {f"3.3.{n}" for n in range(1, 7)} |
                        {f"3.3.7({n})" for n in range(1, 6)} |
                        {f"3.4.{n}" for n in range(1, 14)})
    indexed_results = [r["result"] for r in source_index]
    source_index_errors = []
    if set(indexed_results) != expected_results or len(indexed_results) != len(expected_results):
        source_index_errors.append("Numbered source-result inventory is incomplete or duplicated")
    for entry in source_index:
        if not entry["nodes"] or not entry["sources"]:
            source_index_errors.append([entry["result"], "missing nodes or exact source pages"])
        for label in entry["nodes"]:
            if label not in nodes:
                source_index_errors.append([entry["result"], label, "unknown blueprint node"])
        for anchor in entry["sources"]:
            slug, _, page = anchor.partition(":")
            if not (ROOT.parent / "references" / slug / "tex" / (page + ".tex")).exists():
                source_index_errors.append([entry["result"], anchor, "missing source page"])
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
    result["summary"].update({"imported_boundary_nodes": len(boundaries),
                              "imported_boundary_errors": len(boundary_errors),
                              "unsupported_source_nodes": len(unsupported_nodes),
                              "indexed_source_results": len(source_index),
                              "source_index_errors": len(source_index_errors)})
    result.update({"imported_boundaries": boundaries,
                   "imported_boundary_errors": boundary_errors,
                   "unsupported_source_nodes": unsupported_nodes,
                   "source_result_index": source_index,
                   "source_index_errors": source_index_errors})
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
             "| Gap | Source | Declaration | Blueprint nodes |", "| --- | --- | --- | --- |"]
    for i, gap in enumerate(gaps, 1):
        labels = ", ".join(gap["nodes"]) or "UNMAPPED"
        lines.append(f"| {i} | `{gap['file']}:{gap['line']}` | `{gap['declaration']}` | {labels} |")
    lines += ["", "Gap locations refer to the current authored modules.",
              "The machine-readable inventory also retains the prior chapters and examples,",
              "whose constants are mapped by exact attachments, explicit anonymous-instance owners,",
              "or actual compiled dependency paths to consuming blueprint nodes. A support mapping",
              "is not a formalizes attachment. Completeness checks every project constant.", ""]
    (ROOT / "docs/obligations.md").write_text("\n".join(lines))
    print(json.dumps(result["summary"], indent=2))
    if (args.require_complete or args.require_closed) and (missing or unknown or dangling or nonstandard
                                 or missing_sources or cycles or false_completion or unmapped_project
                                 or stale_inventory or missing_routes
                                 or source_index_errors
                                 or any(not g["nodes"] for g in gaps)):
        raise SystemExit("Incomplete blueprint coverage; see docs/blueprint-coverage.json")
    if args.require_closed and (gaps or any("sorryAx" in r["axioms"] for r in rows)
                                or any(n["notready"] for n in nodes.values())
                                or unsupported_nodes or boundary_errors):
        raise SystemExit("Unclosed mathematical obligations; see docs/blueprint-coverage.json")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit project-only kernel inventory against the authored mathematical route.

Run declaration_inventory.lean after the build, then run this from the project
root. No dependency source tree or generated graph is scanned. An absent
attachment is reported explicitly, never treated as mathematical completion.
"""

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


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
    for path in sorted((ROOT / "blueprint/src").glob("*.tex")):
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
            nodes[label] = {"file": str(path.relative_to(ROOT)), "uses": uses,
                            "lean": names}
            for name in names:
                attached.setdefault(name, []).append(label)
    return nodes, attached


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    rows = json.loads((ROOT / "docs/declaration-inventory.json").read_text())
    by_name = {r["name"]: r for r in rows}
    nodes, attached = blueprint_nodes()
    sources = {}
    for path in sorted((ROOT / "ArakelovGeometry").rglob("*.lean")) + [ROOT / "ArakelovGeometry.lean"]:
        sources[str(path.relative_to(ROOT)).replace("/", ".")[:-5]] = (
            path, lean_code(path.read_text()))
    gaps = []
    for mod, (path, code) in sources.items():
        for match in re.finditer(r"\b(sorry|admit)\b", code):
            line = code.count("\n", 0, match.start()) + 1
            owners = [r for r in rows if r["module"] == mod and r["line"]
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
        candidates = [n for n in attached if name == n or name.startswith(n + ".")]
        parent = max(candidates, key=len) if candidates else None
        row["blueprint_nodes"] = attached.get(parent, [])
        row["attachment"] = parent
        row["project_dependencies"] = [d for d in row["dependencies"] if d in by_name]
        row["external_dependencies"] = [d for d in row["dependencies"] if d not in by_name]
    missing = [r["name"] for r in target if not r["blueprint_nodes"]]
    unknown = sorted(set(attached) - set(by_name))
    dangling = [(n, d) for n, v in nodes.items() for d in v["uses"] if d not in nodes]
    nonstandard = [(r["name"], a) for r in rows for a in r["axioms"]
                   if a not in {"propext", "Classical.choice", "Quot.sound", "sorryAx"}]
    result = {"summary": {"project_constants": len(rows), "target_constants": len(target),
              "direct_gaps": len(gaps), "sorry_backed_constants": sum("sorryAx" in r["axioms"] for r in rows),
              "blueprint_nodes": len(nodes), "unmapped_target_constants": len(missing),
              "unmapped_direct_gaps": sum(not g["nodes"] for g in gaps)},
              "direct_gaps": gaps, "nodes": nodes, "declarations": rows,
              "unmapped_target": missing, "unknown_attachments": unknown,
              "dangling_dependencies": dangling, "nonstandard_axioms": nonstandard}
    (ROOT / "docs/blueprint-coverage.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    lines = ["# Complete extension obligation inventory", "",
             "Generated by `scripts/blueprint_coverage.py` from the compiled project inventory.",
             "Every project constant, including generated declarations, and every direct dependency",
             "is recorded in `blueprint-coverage.json`. External constants remain library references.",
             "A mapped obligation is still open until its transitive axiom audit is clean.", "",
             f"Project constants: {len(rows)}; extension constants: {len(target)}; direct gaps: {len(gaps)}.",
             f"Sorry-backed constants: {result['summary']['sorry_backed_constants']}; blueprint nodes: {len(nodes)}.",
             f"Unmapped extension constants: {len(missing)}; unmapped gaps: {result['summary']['unmapped_direct_gaps']}.", "",
             "| Gap | Source line | Declaration | Blueprint nodes |", "| --- | --- | --- | --- |"]
    for i, gap in enumerate(gaps, 1):
        labels = ", ".join(gap["nodes"]) or "UNMAPPED"
        lines.append(f"| {i} | {gap['line']} | `{gap['declaration']}` | {labels} |")
    lines += ["", "All gap source lines are in `ArakelovGeometry/AdelicCurve/Extension.lean`.",
              "The machine-readable inventory also retains the prior chapters and examples,",
              "whose constants are audited for axioms even when outside the extension blueprint scope.", ""]
    (ROOT / "docs/obligations.md").write_text("\n".join(lines))
    print(json.dumps(result["summary"], indent=2))
    if args.require_complete and (missing or unknown or dangling or nonstandard
                                 or any(not g["nodes"] for g in gaps)):
        raise SystemExit("Incomplete blueprint coverage; see docs/blueprint-coverage.json")


if __name__ == "__main__":
    main()

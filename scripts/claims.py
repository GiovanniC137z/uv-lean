#!/usr/bin/env python3
"""Reproduce the complete inventory of labeled theorem-like source environments."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "7e9a9aca1a1f2d757ce99614c50e9a05662ca05c969253af29cb3c40d2d9a340"
PROJECT_DIRS = {"jordan": ROOT / "jordan"}
PROJECT_PINS = {
    "jordan": {
        "toolchain": "leanprover/lean4:v4.32.2",
        "dependencies": {
            "mathlib": "905b95818eb32af7874a58b427f50c1711a5e96c",
            "schoenflies-lean": "05a43d29cde026618777db3d4e4316204ccca237",
        },
    },
}


def companion_project(name):
    """Read a separately compiled proof project's own theorem inventory.

    This validates source references, not proof transport: each project's
    complete build and transitive axiom audit must run with its own toolchain.
    The root audit and its theorem set remain independent and unchanged.
    """
    if name not in PROJECT_DIRS:
        raise SystemExit(f"Unknown Lean proof project: {name}")
    directory = PROJECT_DIRS[name]
    if not directory.is_dir():
        raise SystemExit(f"Missing Lean proof project: {name}")
    toolchain = (directory / "lean-toolchain").read_text().strip()
    config = tomllib.loads((directory / "lakefile.toml").read_text())
    dependencies = {entry["name"]: entry.get("rev") for entry in config.get("require", [])}
    actual = {"toolchain": toolchain, "dependencies": dependencies}
    if actual != PROJECT_PINS[name]:
        raise SystemExit(f"Changed toolchain/dependency pins for Lean project {name}: {actual}")
    manifest = json.loads((directory / "lake-manifest.json").read_text())
    locked = {entry["name"].strip("«»"): entry.get("rev")
              for entry in manifest.get("packages", [])}
    if any(locked.get(dep) != rev for dep, rev in actual["dependencies"].items()):
        raise SystemExit(f"Changed locked dependency revisions for Lean project {name}")
    script = directory / "scripts" / "audit.py"
    if not script.is_file():
        raise SystemExit(f"Missing theorem inventory for Lean project {name}")
    spec = importlib.util.spec_from_file_location(f"uv_claim_project_{name}", script)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load theorem inventory for Lean project {name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return set(module.theorem_names()), actual


def theorem_references(refs, location):
    if not isinstance(refs, list) or any(not isinstance(ref, str) for ref in refs):
        raise SystemExit(f"Expected theorem-name list in {location}")
    if len(set(refs)) != len(refs):
        raise SystemExit(f"Duplicate theorem references in {location}")
    return set(refs)


def extract():
    source = ROOT / "paper" / "UV.tex"
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise SystemExit("Source differs from the uploaded document; update provenance explicitly")
    text = raw.decode()
    notes = json.loads((ROOT / "verification.json").read_text())
    pattern = re.compile(
        r"\\begin\{(theorem|proposition|lemma|corollary|assumption|definition)\}"
        r"(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}"
    )
    claims = []
    for match in pattern.finditer(text):
        kind, title, label = match.groups()
        end = text.index(r"\end{" + kind + "}", match.end())
        record = {
            "label": label, "kind": kind, "title_tex": " ".join((title or "").split()),
            "source_line": text.count("\n", 0, match.start()) + 1,
            "statement_tex": text[match.end():end].strip(),
            "status": "assumption" if kind == "assumption" else
                      "definition" if kind == "definition" else "pending",
            "lean": [],
            "lean_projects": {},
            "scope": "Not yet formalized.",
        }
        record.update(notes.get(label, {}))
        claims.append(record)
    starts = re.findall(r"\\begin\{(?:theorem|proposition|lemma|corollary|assumption|definition)\}", text)
    if len(starts) != len(claims):
        raise SystemExit("An environment was not inventoried")
    labels = {c["label"] for c in claims}
    if set(notes) - labels:
        raise SystemExit(f"Unknown source labels: {set(notes) - labels}")
    from audit import theorem_names
    names = set(theorem_names())
    project_names, project_pins = {}, {}
    for c in claims:
        if c["status"] not in {"partial", "pending", "assumption", "definition", "verified"}:
            raise SystemExit(f"Unknown status for {c['label']}")
        if theorem_references(c["lean"], c["label"]) - names:
            raise SystemExit(f"Unknown Lean theorem in {c['label']}")
        projects = c["lean_projects"]
        if not isinstance(projects, dict):
            raise SystemExit(f"Expected Lean proof-project map in {c['label']}")
        for project, refs in projects.items():
            if project not in project_names:
                project_names[project], project_pins[project] = companion_project(project)
            if not refs:
                raise SystemExit(f"Empty proof-project evidence in {c['label']}: {project}")
            if theorem_references(refs, f"{c['label']} / {project}") - project_names[project]:
                raise SystemExit(f"Unknown Lean theorem in {c['label']} / {project}")
        if c["status"] == "verified" and not (c["lean"] or projects):
            raise SystemExit(f"Unsupported verified claim: {c['label']}")
    return {"source": "paper/UV.tex", "sha256": SOURCE_SHA,
            "project_pins": dict(sorted(project_pins.items())), "claims": claims}


def markdown(data):
    counts = {}
    for c in data["claims"]:
        counts[c["status"]] = counts.get(c["status"], 0) + 1
    lines = [
        "# Source claim inventory", "",
        "Generated by `python3 scripts/claims.py --write` from the unchanged upload.", "",
        "A **partial** entry means only the stated component is checked. It does not certify the complete source result.", "",
        f"{len(data['claims'])} environments: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())) + ".", "",
        "| Source label | Result | Status | Checked scope and remaining work |",
        "| --- | --- | --- | --- |",
    ]
    for c in data["claims"]:
        title = c["title_tex"].replace("|", "\\|")
        scope = c["scope"].replace("|", "\\|")
        if c["lean_projects"]:
            links = ", ".join(f"[{name}](../{name}/)" for name in sorted(c["lean_projects"]))
            scope += f" Independent proof project: {links}."
        lines.append(
            f"| [{c['label']}](../paper/UV.tex#L{c['source_line']}) | {title} | {c['status']} | {scope} |"
        )
    if data["project_pins"]:
        lines += ["", "Companion proof projects are built and audited separately; compiled proofs are not transported across Lean versions."]
        for name, pins in data["project_pins"].items():
            dependencies = "; ".join(f"{dep} `{rev}`" for dep, rev in pins["dependencies"].items())
            lines += ["", f"- [{name}](../{name}/): `{pins['toolchain']}`; {dependencies}."]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = extract()
    files = {
        ROOT / "claims.json": json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        ROOT / "docs" / "claims.md": markdown(data),
    }
    for path, expected in files.items():
        if args.write:
            path.write_text(expected)
        elif not path.exists() or path.read_text() != expected:
            raise SystemExit(f"Stale {path.name}; run python3 scripts/claims.py --write")
    print(f"PASS: {len(data['claims'])} source environments; upload SHA-256 matches")


if __name__ == "__main__":
    main()

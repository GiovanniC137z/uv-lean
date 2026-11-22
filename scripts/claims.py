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
EXPANDED_SHA = "58c593e0f95d55f881f34a4149e72f2b2a27f113d66f5fe1b57e644f475d785a"
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


def review_blocks(source, claims):
    """Locate all prose blocks, including derivations outside numbered results."""
    pattern = re.compile(r"^\\(section|subsection|subsubsection|paragraph|subparagraph)\*?\{", re.M)
    braces = re.compile(r"\\[{}]|[{}]")
    matches = list(pattern.finditer(source))
    headings = [(1, "frontmatter", "Front matter and abstract")]
    for match in matches:
        depth = 1
        end = match.end()
        for token in braces.finditer(source, end):
            if token.group() == "{":
                depth += 1
            elif token.group() == "}":
                depth -= 1
                if depth == 0:
                    end = token.start()
                    break
        if depth != 0:
            raise SystemExit("Unclosed expanded manuscript heading")
        headings.append((source.count("\n", 0, match.start()) + 1, match.group(1),
                         " ".join(source[match.end():end].split())))
    end_lines = [start - 1 for start, _, _ in headings[1:]] + [len(source.splitlines())]
    blocks = []
    for (start, kind, title), end in zip(headings, end_lines, strict=True):
        blocks.append({
            "kind": kind,
            "title_tex": title,
            "start_line": start,
            "end_line": end,
            "claim_labels": [
                c["label"] for c in claims if start <= c["source_line"] <= end
            ],
        })
    return blocks


def extract(source_name="paper/UV.tex", source_sha=SOURCE_SHA,
            notes_name="verification.json", baseline=None):
    source = ROOT / source_name
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != source_sha:
        raise SystemExit(f"{source_name} differs from the uploaded document; update provenance explicitly")
    text = raw.decode()
    notes = json.loads((ROOT / notes_name).read_text())
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
        entry = notes.get(label, {})
        if set(entry) - {"status", "scope", "lean", "lean_projects"}:
            raise SystemExit(f"Unexpected verification fields in {notes_name}: {label}")
        record.update(entry)
        if baseline is not None:
            if kind == "assumption" and not entry:
                record["scope"] = "Explicit source assumption. Conclusions using it remain conditional."
            if kind == "definition" and not entry:
                record["scope"] = "Source definition. Its uses are audited with the corresponding results."
            previous = baseline.get(label)
            record["statement_change"] = (
                "new" if previous is None else
                "unchanged" if previous["kind"] == kind and
                previous["statement_tex"].split() == record["statement_tex"].split() else
                "revised"
            )
        claims.append(record)
    starts = re.findall(r"\\begin\{(?:theorem|proposition|lemma|corollary|assumption|definition)\}", text)
    if len(starts) != len(claims):
        raise SystemExit("An environment was not inventoried")
    labels = {c["label"] for c in claims}
    if len(labels) != len(claims):
        raise SystemExit(f"Duplicate claim labels in {source_name}")
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
        if c["status"] in {"verified", "partial"} and not (c["lean"] or projects):
            raise SystemExit(f"Unsupported proof status for {c['label']}")
        if c["kind"] in {"assumption", "definition"} and c["status"] != c["kind"]:
            raise SystemExit(f"Source premise or definition assigned proof status: {c['label']}")
    result = {"source": source_name, "sha256": source_sha,
              "project_pins": dict(sorted(project_pins.items())), "claims": claims}
    if baseline is not None:
        result["review_blocks"] = review_blocks(text, claims)
    return result


def markdown(data):
    expanded = data["source"] != "paper/UV.tex"
    counts = {}
    for c in data["claims"]:
        counts[c["status"]] = counts.get(c["status"], 0) + 1
    lines = [
        "# Expanded manuscript claim inventory" if expanded else "# Source claim inventory", "",
        "Generated by `python3 scripts/claims.py --write` from the unchanged upload.", "",
        "A **partial** entry means only the stated component is checked. It does not certify the complete source result.", "",
        f"{len(data['claims'])} environments: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())) + ".", "",
        "| Source label | Result | Status | Checked scope and remaining work |",
        "| --- | --- | --- | --- |",
    ]
    if expanded:
        lines[4:4] = [
            "This inventory covers labeled theorem-like environments in the expanded upload. "
            "Matching labels or statement text alone do not establish correspondence with the archived proof. "
            "See [expanded scope](expanded-scope.md) for unnumbered material and remaining work.", "",
        ]
    for c in data["claims"]:
        title = c["title_tex"].replace("|", "\\|")
        scope = c["scope"].replace("|", "\\|")
        if c["lean_projects"]:
            links = ", ".join(f"[{name}](../{name}/)" for name in sorted(c["lean_projects"]))
            scope += f" Independent proof project: {links}."
        if expanded:
            scope = f"{c['statement_change'].capitalize()} statement. {scope}"
        lines.append(
            f"| [{c['label']}](../{data['source']}#L{c['source_line']}) | {title} | {c['status']} | {scope} |"
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
    expanded = extract("paper/expanded/UV.tex", EXPANDED_SHA, "verification-expanded.json",
                       baseline={c["label"]: c for c in data["claims"]})
    files = {
        ROOT / "claims.json": json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        ROOT / "docs" / "claims.md": markdown(data),
        ROOT / "claims-expanded.json": json.dumps(expanded, indent=2, ensure_ascii=False) + "\n",
        ROOT / "docs" / "claims-expanded.md": markdown(expanded),
    }
    for path, expected in files.items():
        if args.write:
            path.write_text(expected)
        elif not path.exists() or path.read_text() != expected:
            raise SystemExit(f"Stale {path.name}; run python3 scripts/claims.py --write")
    print(f"PASS: {len(data['claims'])} source environments; upload SHA-256 matches")
    print(f"PASS: {len(expanded['claims'])} expanded source environments; upload SHA-256 matches")


if __name__ == "__main__":
    main()

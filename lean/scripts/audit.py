#!/usr/bin/env python3
"""Build the project and audit every public theorem in its Lean source modules."""
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LIB = "ErdosVolume"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"'([\w.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
INPUTS = re.compile(r"INPUTS\|([\w.']+)\|([^|\n]*)\|END")


def claims():
    rows = {}
    for path in sorted((ROOT / LIB).rglob("*.lean")):
        scopes = []
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            block = re.fullmatch(r"(namespace|section|end) ([\w.]+)", line)
            if block:
                kind, name = block.groups()
                if kind == "end":
                    if not scopes or scopes.pop()[1] != name:
                        raise ValueError(f"Unmatched scope at {path}:{line_number}")
                else:
                    scopes.append((kind, name))
                continue
            declaration = re.match(r"(?:theorem|lemma) ([\w']+)\b", line)
            if declaration:
                namespace = [name for kind, name in scopes if kind == "namespace"]
                name = ".".join([*namespace, declaration[1]])
                if name in rows:
                    raise ValueError(f"Duplicate theorem {name}")
                rows[name] = {"name": name, "file": str(path.relative_to(ROOT)), "line": line_number}
        if scopes:
            raise ValueError(f"Unclosed scopes in {path}")
    if not rows:
        raise ValueError("No public theorem declarations found")
    return rows


def write_if_changed(path, data):
    if not path.exists() or path.read_text() != data:
        path.write_text(data)


def parse(lines, expected):
    parsed = {}
    for name, values in lines:
        if name in parsed:
            raise ValueError(f"Duplicate Lean output for {name}")
        parsed[name] = sorted(value.strip() for value in values.split(",") if value.strip())
    if set(parsed) != set(expected):
        raise ValueError(f"Lean output differs from inventory: {sorted(set(parsed) ^ set(expected))}")
    return parsed


def main():
    rows = claims()
    helper = (ROOT / "scripts/audit_inputs.lean.inc").read_text()
    queries = ["import ErdosVolume", "import Lean", helper]
    for name in rows:
        queries.extend([f"#print axioms {name}", f"run_cmd ErdosVolumeAudit.report ``{name}"])
    write_if_changed(ROOT / "Audit.lean", "\n".join(queries) + "\n")
    subprocess.run(["lake", "--no-cache", "build", LIB], cwd=ROOT, check=True)
    result = subprocess.run(["lake", "env", "lean", "-j1", "Audit.lean"], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    axioms = parse(AXIOMS.findall(result.stdout), rows)
    inputs = parse(INPUTS.findall(result.stdout), rows)
    table = ["| Theorem | Status | Explicit analytic inputs |", "|---|---|---|"]
    counts = Counter()
    for name, row in rows.items():
        extra = set(axioms[name]) - STANDARD
        if extra - {"sorryAx"}:
            status = "VIOLATION"
        elif "sorryAx" in extra:
            status = "OPEN"
        elif inputs[name]:
            status = "PROVED GIVEN"
        else:
            status = "PROVED"
        row.update(status=status, axioms=axioms[name], analytic_inputs=inputs[name])
        counts[status] += 1
        table.append(f"| [{name}]({row['file']}#L{row['line']}) | {status} | {', '.join(inputs[name])} |")
    summary = ", ".join(f"{n} {status}" for status, n in sorted(counts.items()))
    report = ["# Lean theorem audit", "", summary, "",
              "Counts include public helper theorems. Each status applies to the full linked statement.",
              "The source inventory and paper line map distinguish the printed claims from their supporting lemmas.",
              "", *table]
    write_if_changed(ROOT / "AUDIT.md", "\n".join(report) + "\n")
    write_if_changed(ROOT / "CLAIMS.json", json.dumps(list(rows.values()), indent=2, ensure_ascii=False) + "\n")
    print(summary)
    if counts["VIOLATION"]:
        raise SystemExit("Unexpected axioms in the imported project")


if __name__ == "__main__":
    main()

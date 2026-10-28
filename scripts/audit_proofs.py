#!/usr/bin/env python3
"""Rebuild the project and reject non-foundational axioms in registered results."""
import argparse
import json
from pathlib import Path
import subprocess

from proof_search import axiom_check

THEOREMS = [
    "LeanProofs.persistent_value",
    "LeanProofs.boundsAll_of_cardinal_lt_cof",
    "LeanProofs.compact_intersection_hits",
    "LeanProofs.compact_intersection_hits_of_lt_cof",
    "LeanProofs.bad_iInter_of_lt_cof",
    "LeanProofs.nat_tails_counterexample",
    "LeanProofs.nat_tails_have_no_common_lower_member",
    "Search.persistent_value",
    "Search.persistence_implies_bounds",
    "LeanProofs.boundsAll_iff_persistence",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = subprocess.run([args.lake, "--wfail", "build"], cwd=root, capture_output=True, text=True)
    print(build.stdout + build.stderr, end="")
    if build.returncode:
        return build.returncode
    work = root / ".proof-search-work"
    work.mkdir(exist_ok=True)
    path = work / "Audit.lean"
    path.write_text("module\nimport LeanProofs\n\n" + "\n".join(
        "#print axioms " + theorem for theorem in THEOREMS) + "\n")
    proc = subprocess.run([args.lake, "env", "lean", "--json", str(path)],
                          cwd=root, capture_output=True, text=True)
    messages = []
    for line in proc.stdout.splitlines():
        try:
            messages.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    report = {"lean": subprocess.check_output(
        [args.lake, "env", "lean", "--version"], cwd=root, text=True).strip(),
        "build_exit_code": build.returncode, "audit_exit_code": proc.returncode,
        "theorems": {}}
    for theorem in THEOREMS:
        passed, axioms = axiom_check(messages, theorem)
        report["theorems"][theorem] = {"passed": passed, "axioms": axioms}
    report["passed"] = proc.returncode == 0 and all(
        v["passed"] for v in report["theorems"].values())
    rendered = json.dumps(report, indent=2) + "\n"
    print(rendered, end="")
    if args.output:
        Path(args.output).write_text(rendered)
    if not report["passed"]:
        print(proc.stdout + proc.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

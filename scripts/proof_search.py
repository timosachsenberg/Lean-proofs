#!/usr/bin/env python3
"""Bounded best-first tactic search, checked by a pinned local Lean installation.

The policy is an explicit, task-specific tactic catalog supplied by a human or
model. This is a small search baseline, not reinforcement learning or AlphaProof.
Incomplete nodes are recorded only as search states. A solution must compile
without errors AND have only the three allowed foundational axioms.
"""
from __future__ import annotations

import argparse
import hashlib
import heapq
import itertools
import json
from pathlib import Path
import re
import subprocess
import time

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def axiom_check(messages: list[dict], theorem: str) -> tuple[bool, list[str]]:
    for msg in messages:
        data = msg.get("data", "")
        if f"'{theorem}'" not in data:
            continue
        if "does not depend on any axioms" in data:
            return True, []
        match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", data)
        if match:
            axioms = [a.strip() for a in match.group(1).split(",") if a.strip()]
            return set(axioms) <= ALLOWED_AXIOMS, axioms
    return False, []


def run_search(args: argparse.Namespace) -> int:
    root = Path(__file__).resolve().parents[1]
    task_path = Path(args.task).resolve()
    task_bytes = task_path.read_bytes()
    task = json.loads(task_bytes)
    work = root / ".proof-search-work" / task["name"]
    work.mkdir(parents=True, exist_ok=True)
    output = Path(args.output).resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError("Output directory is not empty; use a new path to preserve earlier runs")
    output.mkdir(parents=True, exist_ok=True)
    serial = itertools.count()
    queue = [(0.0, next(serial), [], None)]
    seen: set[str] = set()
    attempts = 0
    run_start = time.monotonic()
    source = work / "Candidate.lean"
    final_file = None

    # Input is a trusted local research task, not an untrusted execution service.
    # These checks catch accidental proof holes and bypasses in our own proposals.
    forbidden = r"\b(sorry|admit|axiom|native_decide|run_tac)\b|skipKernelTC"
    for entry in task["tactics"]:
        if re.search(forbidden, entry["text"]):
            raise ValueError("Tactic catalog contains a forbidden proof shortcut")

    with (output / "attempts.jsonl").open("w") as log:
        while queue and attempts < args.max_attempts:
            cost, node, steps, parent = heapq.heappop(queue)
            body = "\n".join("  " + line for s in task.get("initial", []) + steps
                             for line in s.splitlines())
            code = (task["preamble"] + "\n" + task["statement"] + " := by\n" +
                    body + "\n  all_goals skip\n\n#print axioms " + task["theorem"] + "\n")
            source.write_text(code)
            started = time.monotonic()
            try:
                proc = subprocess.run([args.lake, "env", "lean", "--json", str(source)],
                                      cwd=root, text=True, capture_output=True,
                                      timeout=args.timeout)
                messages = []
                for line in proc.stdout.splitlines():
                    try:
                        messages.append(json.loads(line))
                    except json.JSONDecodeError:
                        pass
                errors = [m.get("data", "") for m in messages
                          if m.get("severity") == "error"]
                audit_ok, axioms = axiom_check(messages, task["theorem"])
                solved = proc.returncode == 0 and not errors and audit_ok
                frontier = bool(errors) and all(e.startswith("unsolved goals") for e in errors)
                state = "\n\n".join(errors)
                status = "proved" if solved else "frontier" if frontier else "rejected"
                record = dict(node=node, parent=parent, cost=cost, steps=steps,
                              status=status, returncode=proc.returncode,
                              messages=messages, stderr=proc.stderr, axioms=axioms)
            except subprocess.TimeoutExpired:
                solved, frontier, state = False, False, ""
                record = dict(node=node, parent=parent, cost=cost, steps=steps, status="timeout")
            attempts += 1
            record["elapsed_seconds"] = round(time.monotonic() - started, 3)
            log.write(json.dumps(record, ensure_ascii=False) + "\n")
            log.flush()
            print(f"{attempts}: {record['status']} depth={len(steps)} cost={cost:g}", flush=True)
            if solved:
                final_file = output / "Proof.lean"
                final_file.write_text(code)
                break
            if frontier and state not in seen and len(steps) < args.max_depth:
                seen.add(state)
                for candidate in task["tactics"]:
                    if any(t not in state for t in candidate.get("requires", [])):
                        continue
                    if any(t in state for t in candidate.get("excludes", [])):
                        continue
                    heapq.heappush(queue, (cost + candidate.get("cost", 1), next(serial),
                                          steps + [candidate["text"]], node))
    summary = dict(task=task["name"], theorem=task["theorem"],
                   task_sha256=hashlib.sha256(task_bytes).hexdigest(),
                   status="proved" if final_file else "budget_exhausted_or_no_frontier",
                   attempts=attempts, distinct_frontiers=len(seen),
                   elapsed_seconds=round(time.monotonic() - run_start, 3),
                   policy="explicit model-supplied tactic catalog; no weight updates",
                   max_attempts=args.max_attempts, max_depth=args.max_depth,
                   timeout_seconds=args.timeout, proof="Proof.lean" if final_file else None)
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0 if final_file else 2


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task")
    parser.add_argument("--output", required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--max-attempts", type=int, default=80)
    parser.add_argument("--max-depth", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=30)
    raise SystemExit(run_search(parser.parse_args()))

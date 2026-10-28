# Lean proofs: square compactness investigation

Formal checkpoints for the investigation of square compactness and the
κ-complete filter extension principle. Lean and mathlib are pinned to **v4.35.0**;
`lake-manifest.json` pins the transitive dependencies.

## Current status

The first checkpoint verifies:

- persistence of a value when all disappearance stages have a common bound;
- that cardinality below the cofinality supplies this bound;
- the resulting intersection theorem for decreasing compact sets and closed fibres;
- two natural-number counterchecks showing why a decreasing chain alone does
  not provide the bound required in the earlier handwritten argument.

The second checkpoint adds an explicit best-first tactic search and its raw
Lean feedback. Two searches succeeded in **48** and **25** candidate checks.
Their proofs establish the two directions of `boundsAll_iff_persistence`:
having a common upper bound for every value-indexed family is equivalent to
persistence for all antitone predicates. This is a logical characterization,
not a solution of the special inverse-system problem.
The initial coordinate-system search checked 17 candidates and left an open
cofinality bound on one branch. Its failure is recorded without claiming a
counterexample or an impossibility result.

These are baseline formalizations, with no claim of mathematical novelty.
**SqC ⇒ strong compactness has not been proved or refuted.**
`LeanProofs.Definitions.MainConjecture` records a universe-relative research
target as a definition of a proposition, not as an axiom or proved theorem.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
python3 scripts/audit_proofs.py
```

The optional `scripts/compat/proc_self.c` adapts executable-path lookup in
containers exposing `/proc/self/exe` but not `/proc/<pid>/exe`. Normal machines
do not need it. It changes no mathematical code or kernel checks.

## Files

- `LeanProofs/Definitions.lean`: open-cover and filter-extension formulations.
- `LeanProofs/CompactWitness.lean`: proved intersection lemmas.
- `LeanProofs/Counterexamples.lean`: proved combinatorial regression examples.
- `LeanProofs/Persistence.lean`: equivalence assembled from the searched proofs.
- `LeanProofs/CoordinateSystem.lean`: explicit hypotheses and the unproved small-limit target.
- `LeanProofs/Search/`: the proofs produced by the search runs.
- `search/tasks/`: complete statements, tactic catalogs, and priorities.
- `results/2026-10-28/`: raw candidate logs, complete proofs, and axiom audits.
- `research/STATUS.md`: precise boundary between proved and open statements.

## Reproduce a search

```sh
python3 scripts/proof_search.py search/tasks/persistent_value.json \
  --output results/my-persistence-run --max-attempts 50
python3 scripts/proof_search.py search/tasks/persistence_implies_bounds.json \
  --output results/my-converse-run --max-attempts 50
```

Use a fresh output directory for each run; earlier logs are never overwritten.
The controller explores tactic sequences by increasing cumulative cost, reads
Lean's remaining goals, discards invalid steps, and avoids repeated states.
Every successful candidate must compile and pass an axiom dependency check.
The tactic catalog and priorities were supplied by the assisting model. There
is no learned value network, autonomous model API, weight update, or background
training service. This is a reproducible baseline for model-guided proof search,
not a reproduction of AlphaProof.

An incomplete search node may contain `sorryAx` in Lean's diagnostic recovery
environment. Such nodes are recorded as unfinished and cannot pass the final
axiom audit. No generated proof containing that axiom is accepted or imported.
The `reject_false_control` task confirms that an invalid proposed proof is
rejected; its unsuccessful search is not itself a proof of a negation.

GitHub Actions rebuilds the project and audits all registered theorem dependencies
on pushes and pull requests. Local audits also fail on build warnings.

No unfinished theorem is admitted with `sorry` and no desired conclusion is
introduced as an axiom. Formal verification establishes a precisely stated
implication; it does not establish novelty or the adequacy of a conjecture's
translation to the original mathematical question.

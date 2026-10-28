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
```

The optional `scripts/compat/proc_self.c` adapts executable-path lookup in
containers exposing `/proc/self/exe` but not `/proc/<pid>/exe`. Normal machines
do not need it. It changes no mathematical code or kernel checks.

## Files

- `LeanProofs/Definitions.lean`: open-cover and filter-extension formulations.
- `LeanProofs/CompactWitness.lean`: proved intersection lemmas.
- `LeanProofs/Counterexamples.lean`: proved combinatorial regression examples.

No unfinished theorem is admitted with `sorry` and no desired conclusion is
introduced as an axiom. Formal verification establishes a precisely stated
implication; it does not establish novelty or the adequacy of a conjecture's
translation to the original mathematical question.

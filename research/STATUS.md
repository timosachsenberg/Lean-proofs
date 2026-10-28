# Research checkpoint — 28 October 2026

## Verified

All statements below have complete Lean proofs. See the recorded axiom audits.

For a preorder `A` of stages and a type `S` of possible values, let

    BoundsAll A S := ∀ f : S → A, ∃ a, ∀ s, f s ≤ a.

For every antitone predicate `P a s`, if each stage has some value and
`BoundsAll A S` holds, then one value survives at every stage. Conversely,
if this persistence conclusion holds for **every** antitone predicate, then
`BoundsAll A S` holds. The converse uses `P a s := ¬ (f s ≤ a)` for a purported
unbounded family `f`. Both directions were checked by the recorded tactic
searches; the candidate tactics, including the suggested intermediate claims,
were supplied by the assisting model.

For a directed preorder `A`, decreasing compact sets `H a` in a Hausdorff space,
and closed sets `F s`, suppose each `H a` meets some `F s`. Under `BoundsAll A S`,
the intersection of all `H a` meets one `F s`. The proof first fixes a persistent
`s`, then applies compactness to the closed intersections `H a ∩ F s`.

For a linear order of stages, `|S| < cof(A)` implies `BoundsAll A S`.
Taking `S` to be the subtype `p_i[R]` and `F s` to be a coordinate fibre proves
`bad_iInter_of_lt_cof`. Thus the cardinal restriction is on **relevant coordinate
values** `p_i[R]`, not necessarily on the whole coordinate space.
In particular, the informal assumptions `|p_i[R]| < κ ≤ cof(A)` suffice.

Two proofs about tails of natural numbers certify the elementary obstruction:
every tail is nonempty, their intersection is empty, and no member of this
descending chain is a lower member for the whole chain.

## What this does not prove

- The high-cofinality theorem does not cover a limit stage of cofinality below κ
  when its relevant coordinate images are too large.
- The equivalence quantifies over arbitrary antitone predicates. It does not
  rule out a stronger theorem using the extra structure of an inverse system.
- The natural-number examples are not compact inverse-system counterexamples.
- The asserted `2^κ` lower bound from the old handwritten binary-tree recursion
  remains unproved. No limit stage has been repaired by silently treating a
  chain as a `<κ`-directed family.
- No theorem in this project derives filter extension from square compactness.
- Mathematical novelty is not claimed for these baseline lemmas.

## Small-limit search target

Investigate whether the specific predicates

    P_i(a,z) := (H_a ∩ p_i⁻¹({z})).Nonempty,   z ∈ p_i[R],

have an additional persistence property at small-cofinality limits when the
coordinates form the actual `<κ`-directed inverse system, `R` is saturated,
and all compact witnesses are disjoint from `R`.

`CoordinateSystem.lean` now defines small directedness, compatibility, joint
point separation, and saturation. The search task `small_limit_coordinate_system`
additionally includes continuity, a compact Hausdorff ambient space, Hausdorff
coordinate spaces, small relevant coordinate images, a small linear order of
stages without a maximum, and compact witnesses disjoint from `R`.
The hypotheses are explicit in `search/tasks/small_limit_coordinate_system.json`.

These are the coordinate-level hypotheses from the notes. The encoding does
not identify the ambient space with a full inverse limit, provide bonding maps,
or construct Stone–Čech coordinate spaces. Consequently this is a general
candidate lemma; it is not a formalization of every detail of the original
construction. `Bad` itself says only that no one coordinate separates a set
from `R`. A bounded search of the candidate is recorded separately from the
successful baseline searches. Failure of that search does not refute the lemma.

The first coordinate-system run checked 17 candidates and exhausted the
available branches of its small tactic catalog. Applying the existing
high-cofinality theorem left the obligation

    Cardinal.mk (p i '' R) < Order.cof A.

The available hypotheses only bound that cardinal by κ, while `|A| < κ`.
This is a remaining goal on **that proof branch**, not a theorem that every
possible proof needs the same bound. The run did not discover how to use
compatibility or saturation to avoid it. The full remaining context is saved
in `results/2026-10-28/small-limit-coordinate-system/remaining-goal.txt`.

`MainConjecture` records the inaccessible-cardinal version of the universe-relative
SqC-to-filter-extension target as a proposition. Adequacy of this formalization,
universe scope, and the reductions connecting it to the original problem still
require mathematical review. The main implication has not been proved or refuted.

## Search evidence

| Run | Candidate checks | Outcome |
| --- | ---: | --- |
| `persistent-value` | 48 | Complete proof; only standard foundational axioms |
| `persistence-implies-bounds` | 25 | Complete proof; only standard foundational axioms |
| `reject-false-control` | 2 | Invalid proof rejected; no accepted theorem |
| `small-limit-coordinate-system` | 17 | No proof found with the supplied tactic catalog |

`attempts.jsonl` records the actual steps, parent nodes, Lean diagnostics, costs,
and elapsed times. `summary.json` includes the task-file hash. Complete proofs
are retained alongside the logs and imported into the project under
`LeanProofs/Search/` (omitting only the final no-op and diagnostic print).
Search was performed with a fixed explicit tactic catalog;
there was no reinforcement-learning training run.

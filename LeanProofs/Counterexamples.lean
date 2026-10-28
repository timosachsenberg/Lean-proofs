module

public import Mathlib.Tactic

/-! Regression examples for the missing small-cofinality limit step.
These are combinatorial examples, not topological counterexamples to SqC.
-/

@[expose] public section

namespace LeanProofs

/-- Each tail has a point, but there is no point in every tail. -/
theorem nat_tails_counterexample :
    (∀ n : ℕ, ∃ m : ℕ, n ≤ m) ∧ ¬ (∃ m : ℕ, ∀ n : ℕ, n ≤ m) := by
  constructor
  · exact fun n => ⟨n, le_rfl⟩
  · rintro ⟨m, hm⟩
    exact Nat.not_succ_le_self m (hm (m + 1))

/-- An infinite descending chain need not have a lower member in the chain.
This is the exact directedness mistake in the earlier binary-tree argument. -/
theorem nat_tails_have_no_common_lower_member :
    ¬ ∃ b : ℕ, ∀ n : ℕ, {m : ℕ | b ≤ m} ⊆ {m : ℕ | n ≤ m} := by
  rintro ⟨b, hb⟩
  exact Nat.not_succ_le_self b (hb (b + 1) (show b ≤ b from le_rfl))

end LeanProofs

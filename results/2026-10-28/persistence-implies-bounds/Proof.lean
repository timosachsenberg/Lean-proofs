module

public import Mathlib.Tactic

public section
universe u v
theorem Search.persistence_implies_bounds {A : Type u} [Preorder A] {S : Type v}
    (hpersist : ∀ P : A → S → Prop,
      (∀ ⦃a b⦄, a ≤ b → ∀ s, P b s → P a s) →
      (∀ a, ∃ s, P a s) → ∃ s, ∀ a, P a s) :
    ∀ f : S → A, ∃ a, ∀ s, f s ≤ a := by
  classical
  intro f
  by_contra h
  push Not at h
  have hanti : ∀ ⦃a b : A⦄, a ≤ b → ∀ s : S, (¬ f s ≤ b) → ¬ f s ≤ a := by
    intro a b hab s hs hsa
    exact hs (le_trans hsa hab)
  obtain ⟨s, hs⟩ := hpersist (fun a s => ¬ f s ≤ a) hanti h
  exact hs (f s) le_rfl
  all_goals skip

#print axioms Search.persistence_implies_bounds

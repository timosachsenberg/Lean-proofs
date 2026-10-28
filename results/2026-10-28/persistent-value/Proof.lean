module

public import Mathlib.Tactic

public section
universe u v
theorem Search.persistent_value {A : Type u} [Preorder A] {S : Type v}
    (P : A → S → Prop)
    (hanti : ∀ ⦃a b⦄, a ≤ b → ∀ s, P b s → P a s)
    (hbound : ∀ f : S → A, ∃ a, ∀ s, f s ≤ a)
    (hne : ∀ a, ∃ s, P a s) : ∃ s, ∀ a, P a s := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  obtain ⟨b, hb⟩ := hbound f
  obtain ⟨s, hs⟩ := hne b
  exact hf s (hanti (hb s) s hs)
  all_goals skip

#print axioms Search.persistent_value

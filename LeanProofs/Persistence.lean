module

public import LeanProofs.CompactWitness
public import LeanProofs.Search.PersistentValue
public import LeanProofs.Search.PersistenceImpliesBounds

public section

namespace LeanProofs

universe u v

/-- The common-bound condition is exactly what is needed for persistence for
ALL antitone predicates. This does not decide persistence for the special
predicates arising from compact fibres in an inverse system. -/
theorem boundsAll_iff_persistence {A : Type u} [Preorder A] {S : Type v} :
    BoundsAll A S ↔
      ∀ P : A → S → Prop,
        (∀ ⦃a b⦄, a ≤ b → ∀ s, P b s → P a s) →
        (∀ a, ∃ s, P a s) → ∃ s, ∀ a, P a s := by
  constructor
  · intro h P hanti hne
    exact Search.persistent_value P hanti h hne
  · exact Search.persistence_implies_bounds

end LeanProofs

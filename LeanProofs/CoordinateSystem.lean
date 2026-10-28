module

public import LeanProofs.CompactWitness
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

namespace LeanProofs

open Set
universe u

/-- Every set of fewer than κ coordinate indices has an upper bound. -/
def SmallDirected (κ : Cardinal.{u}) (I : Type u) [Preorder I] : Prop :=
  ∀ J : Set I, Cardinal.mk J < κ → ∃ j, ∀ i ∈ J, i ≤ j

/-- The coordinate-level inverse-system assumptions used in the notes.
This does not assert that X is the entire inverse limit or introduce
Stone–Čech spaces. Those would be additional data, not implicit facts. -/
structure CompatibleCoordinates (κ : Cardinal.{u})
    {I X : Type u} [Preorder I] [TopologicalSpace X]
    {Y : I → Type u} [∀ i, TopologicalSpace (Y i)]
    (p : (i : I) → X → Y i) : Prop where
  directed : SmallDirected κ I
  continuous : ∀ i, Continuous (p i)
  compatible : ∀ ⦃i j⦄, i ≤ j → ∀ x y, p j x = p j y → p i x = p i y
  separates : ∀ x y, (∀ i, p i x = p i y) → x = y

/-- Membership is determined by belonging to the image at every coordinate. -/
def CoordinateSaturated {I X : Type u} {Y : I → Type u}
    (p : (i : I) → X → Y i) (R : Set X) : Prop :=
  ∀ x, (∀ i, p i x ∈ p i '' R) → x ∈ R

/-- Candidate small-limit preservation statement for a fixed coordinate
system. This is an UNPROVED proposition, not a theorem or an axiom.
The search tasks spell out the hypotheses when attempting an instance. -/
def SmallLimitPreservation {I X : Type u} [TopologicalSpace X]
    {Y : I → Type u} (κ : Cardinal.{u})
    (p : (i : I) → X → Y i) (R : Set X) : Prop :=
  ∀ (A : Type u) (_ : LinearOrder A) (_ : Nonempty A),
    Cardinal.mk A < κ → ∀ H : A → Set X,
      Antitone H → (∀ a, IsCompact (H a)) →
      (∀ a, Disjoint (H a) R) → (∀ a, Bad p R (H a)) →
      Bad p R (⋂ a, H a)

end LeanProofs

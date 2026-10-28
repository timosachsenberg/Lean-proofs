module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
Universe-relative formulations of the research target. These declarations are
definitions, not proofs of the main implication. All carrier types lie in `Type u`.
The mathematical unrestricted statement is interpreted across universes.
-/

@[expose] public section

namespace LeanProofs

open Set Filter
universe u

/-- Every open cover has a subcover with cardinality strictly below `κ`. -/
def KCompact (κ : Cardinal.{u}) (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), (∀ V ∈ U, IsOpen V) → ⋃₀ U = Set.univ →
    ∃ V : Set (Set X), V ⊆ U ∧ Cardinal.mk V < κ ∧ ⋃₀ V = Set.univ

/-- Square compactness for Hausdorff spaces in one universe. -/
def SquareCompact (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (t : TopologicalSpace X),
    @T2Space X t → @KCompact κ X t → KCompact κ (X × X)

/-- Extension of every proper κ-complete filter to a κ-complete ultrafilter. -/
def FilterExtension (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (F : Filter X), F.NeBot → CardinalInterFilter F κ →
    ∃ U : Ultrafilter X, (U : Filter X) ≤ F ∧ CardinalInterFilter (U : Filter X) κ

/-- The target is recorded as a proposition, with no axiom asserting it. -/
def MainConjecture (κ : Cardinal.{u}) : Prop :=
  Cardinal.IsInaccessible κ → SquareCompact κ → FilterExtension κ

end LeanProofs

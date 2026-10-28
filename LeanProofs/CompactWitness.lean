module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.Tactic

/-! Compact-witness lemmas for the square-compactness investigation. -/

@[expose] public section

namespace LeanProofs

open Set

universe u v w

/-- Every family of stages indexed by `S` has a common upper bound. -/
def BoundsAll (A : Type u) [Preorder A] (S : Type v) : Prop :=
  ∀ f : S → A, ∃ a, ∀ s, f s ≤ a

/-- A value survives at every stage if there are too few possible values for
their individual disappearance times to be unbounded. No topology is used. -/
theorem persistent_value {A : Type u} [Preorder A] {S : Type v}
    (P : A → S → Prop)
    (hanti : ∀ ⦃a b⦄, a ≤ b → ∀ s, P b s → P a s)
    (hbound : BoundsAll A S)
    (hne : ∀ a, ∃ s, P a s) : ∃ s, ∀ a, P a s := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  obtain ⟨b, hb⟩ := hbound f
  obtain ⟨s, hs⟩ := hne b
  exact hf s (hanti (hb s) s hs)

/-- The cardinal/cofinality hypothesis supplies the exact bound used above.
Both indexing types live in the same universe so no cardinal lifts are hidden. -/
theorem boundsAll_of_cardinal_lt_cof {A S : Type u} [LinearOrder A]
    (hcard : Cardinal.mk S < Order.cof A) : BoundsAll A S := by
  intro f
  have hn : ¬ IsCofinal (Set.range f) := by
    intro hcof
    exact (not_le_of_gt hcard) ((Order.cof_le hcof).trans Cardinal.mk_range_le)
  obtain ⟨a, ha⟩ := (BddAbove.of_not_isCofinal hn)
  exact ⟨a, fun s => ha (Set.mem_range_self s)⟩

/-- A decreasing family of compact sets meets one of a boundedly indexed
family of closed sets at every stage, hence its intersection does too.
This packages the compact-fibre argument without assuming the conclusion. -/
theorem compact_intersection_hits {A : Type u} [Preorder A] [IsDirectedOrder A] [Nonempty A]
    {X : Type v} [TopologicalSpace X] [T2Space X] {S : Type w}
    (H : A → Set X) (F : S → Set X)
    (hH : Antitone H) (hc : ∀ a, IsCompact (H a))
    (hF : ∀ s, IsClosed (F s)) (hbound : BoundsAll A S)
    (hhit : ∀ a, ∃ s, (H a ∩ F s).Nonempty) :
    ∃ s, ((⋂ a, H a) ∩ F s).Nonempty := by
  obtain ⟨s, hs⟩ := persistent_value (fun a s => (H a ∩ F s).Nonempty)
    (fun _ _ hab _ h => h.mono (inter_subset_inter_left _ (hH hab))) hbound hhit
  have hant : Antitone (fun a => H a ∩ F s) :=
    fun _ _ hab => inter_subset_inter_left _ (hH hab)
  have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun a => H a ∩ F s) hant.directed_ge hs
    (fun a => (hc a).inter_right (hF s))
    (fun a => (hc a).isClosed.inter (hF s))
  obtain ⟨x, hx⟩ := hne
  refine ⟨s, x, mem_iInter.mpr (fun a => (mem_iInter.mp hx a).1), ?_⟩
  exact (mem_iInter.mp hx (Classical.arbitrary A)).2

/-- The high-cofinality compact-witness rule. The size restriction concerns
the set of relevant values, not necessarily the entire coordinate space. -/
theorem compact_intersection_hits_of_lt_cof
    {A S : Type u} [LinearOrder A] [Nonempty A]
    {X : Type v} [TopologicalSpace X] [T2Space X]
    (H : A → Set X) (F : S → Set X)
    (hH : Antitone H) (hc : ∀ a, IsCompact (H a))
    (hF : ∀ s, IsClosed (F s)) (hcard : Cardinal.mk S < Order.cof A)
    (hhit : ∀ a, ∃ s, (H a ∩ F s).Nonempty) :
    ∃ s, ((⋂ a, H a) ∩ F s).Nonempty :=
  compact_intersection_hits H F hH hc hF (boundsAll_of_cardinal_lt_cof hcard) hhit

/-- No single coordinate separates `H` from `R`. This definition alone does
not assert saturation of `R`, disjointness, or an inverse-system structure. -/
def Bad {I X : Type u} {Y : I → Type u}
    (p : (i : I) → X → Y i) (R H : Set X) : Prop :=
  ∀ i, ∃ x ∈ H, p i x ∈ p i '' R

/-- Coordinate form of the high-cofinality lemma. It applies in particular to
inverse systems, without requiring their bonding maps for this limit rule. -/
theorem bad_iInter_of_lt_cof
    {A I X : Type u} [LinearOrder A] [Nonempty A]
    [TopologicalSpace X] [T2Space X]
    {Y : I → Type u} [∀ i, TopologicalSpace (Y i)] [∀ i, T1Space (Y i)]
    (p : (i : I) → X → Y i) (hp : ∀ i, Continuous (p i))
    (R : Set X) (H : A → Set X)
    (hH : Antitone H) (hc : ∀ a, IsCompact (H a))
    (hcard : ∀ i, Cardinal.mk (p i '' R) < Order.cof A)
    (hbad : ∀ a, Bad p R (H a)) : Bad p R (⋂ a, H a) := by
  intro i
  let F : (p i '' R) → Set X := fun z => p i ⁻¹' {z.val}
  have hF : ∀ z, IsClosed (F z) :=
    fun z => isClosed_singleton.preimage (hp i)
  have hhit : ∀ a, ∃ z, (H a ∩ F z).Nonempty := by
    intro a
    obtain ⟨x, hx, hz⟩ := hbad a i
    exact ⟨⟨p i x, hz⟩, x, hx, rfl⟩
  obtain ⟨z, x, hx, hz⟩ :=
    compact_intersection_hits_of_lt_cof H F hH hc hF (hcard i) hhit
  have heq : p i x = z.val := hz
  exact ⟨x, hx, heq ▸ z.property⟩

end LeanProofs

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selected subgroup tiling and conjugation proofs from PeterssonLevelN.lean,
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.GroupTheory.Coset.Basic

/-! # Fundamental-domain transport for the genuine Petersson pairing -/

namespace Dubon2026

open MeasureTheory
open scoped Pointwise

noncomputable section

private theorem eq_of_mul_out_inv_eq {G : Type*} [Group G] {H : Subgroup G}
    {r₁ r₂ : G ⧸ H} {a b : H}
    (hh : (a : G) * (r₁.out)⁻¹ = (b : G) * (r₂.out)⁻¹) : a = b := by
  have hmem : (r₂.out : G)⁻¹ * r₁.out ∈ H := by
    have he : (b : G)⁻¹ * (a : G) = (r₂.out : G)⁻¹ * (r₁.out : G) := by
      have h2 : (b : G)⁻¹ * ((a : G) * (r₁.out)⁻¹) * r₁.out
          = (b : G)⁻¹ * ((b : G) * (r₂.out)⁻¹) * r₁.out := by rw [hh]
      simpa [mul_assoc] using h2
    rw [← he]; exact H.mul_mem (H.inv_mem b.2) a.2
  obtain rfl : r₁ = r₂ := by
    have : (QuotientGroup.mk r₁.out : G ⧸ H) = QuotientGroup.mk r₂.out := by
      rw [QuotientGroup.eq]; simpa [mul_inv_rev] using H.inv_mem hmem
    simpa using this
  exact Subtype.ext (mul_right_cancel hh)

/-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for a group `G` acting on `α`, then for any subgroup `H ≤ G`, the union of
`[G : H]`-many translates `(q.out)⁻¹ • s` (for `q ∈ G ⧸ H`) is a fundamental
domain for the restricted `H`-action on `α`. -/
theorem fundamentalDomain_subgroup_iUnion_out_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [Countable (G ⧸ H)] {s : Set α}
    (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s) μ := by
  set T : Set α := ⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s with hT_def
  refine ⟨.iUnion fun q ↦ hs.nullMeasurableSet_smul _, ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with τ ⟨g, hg⟩
    set q : G ⧸ H := QuotientGroup.mk g
    have hmem : q.out⁻¹ * g ∈ H := by
      rw [← QuotientGroup.leftRel_apply]; exact Quotient.exact q.out_eq
    refine ⟨⟨q.out⁻¹ * g, hmem⟩, ?_⟩
    show (q.out⁻¹ * g) • τ ∈ T
    rw [mul_smul]
    exact Set.mem_iUnion.mpr ⟨q, Set.smul_mem_smul_set hg⟩
  · intro h₁ h₂ hne
    show AEDisjoint μ ((h₁ : G) • T) ((h₂ : G) • T)
    rw [hT_def]
    simp only [Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff,
      ← mul_smul]
    exact fun q₁ q₂ ↦ hs.aedisjoint fun heq ↦ hne (eq_of_mul_out_inv_eq heq)

private theorem eq_of_mul_transversal {G : Type*} [Group G] {H : Subgroup G}
    {ι : Type*} {r : ι → G}
    (he : Function.Injective (fun i ↦ (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)))
    {i j : ι} {a b : H} (hh : (a : G) * r i = (b : G) * r j) : a = b ∧ i = j := by
  have hmem : (r j : G) * (r i)⁻¹ ∈ H := by
    have he' : (b : G)⁻¹ * (a : G) = (r j : G) * (r i)⁻¹ := by
      have h2 : (b : G)⁻¹ * ((a : G) * r i) * (r i)⁻¹
          = (b : G)⁻¹ * ((b : G) * r j) * (r i)⁻¹ := by rw [hh]
      simpa [mul_assoc] using h2
    rw [← he']
    exact H.mul_mem (H.inv_mem b.2) a.2
  obtain rfl : i = j := he <| by
    show (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H) = QuotientGroup.mk ((r j)⁻¹)
    rw [eq_comm, QuotientGroup.eq]; simpa [inv_inv] using hmem
  exact ⟨Subtype.ext (mul_right_cancel hh), rfl⟩

/-- **Arbitrary-transversal subgroup coset tiling of a fundamental domain.** If `s`
is a fundamental domain for a group `G` acting on `α`, `H ≤ G`, and `r : ι → G` is a
family whose `(r i)⁻¹` represent *all* the left cosets `G ⧸ H` bijectively (`e : ι ≃ G ⧸ H`
with `e i = ⟦(r i)⁻¹⟧`), then `⋃ i, r i • s` is a fundamental domain for the restricted
`H`-action. This generalizes `fundamentalDomain_subgroup_iUnion_out_smul` (the special
case `r i = (i.out)⁻¹` with `e = Equiv.refl`) to an arbitrary complete transversal — needed
when the natural tiling uses geometric representatives that differ from the canonical
`.out` reps by `H`-elements. -/
theorem fundamentalDomain_iUnion_smul_of_transversal
    {G α ι : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [Countable ι]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    {H : Subgroup G} {s : Set α} (hs : IsFundamentalDomain G s μ)
    {r : ι → G} (e : ι ≃ G ⧸ H) (he : ∀ i, e i = (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)) :
    IsFundamentalDomain H (⋃ i, r i • s) μ := by
  have hinj : Function.Injective (fun i ↦ (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)) :=
    fun i j hij ↦ e.injective (by rw [he, he]; exact hij)
  set T : Set α := ⋃ i, r i • s with hT_def
  refine ⟨.iUnion fun i ↦ hs.nullMeasurableSet_smul _, ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with τ ⟨g, hg⟩
    set i : ι := e.symm (QuotientGroup.mk g) with hi_def
    have hmem : (r i) * g ∈ H := by
      have hcoset : (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H) = QuotientGroup.mk g := by
        rw [← he, hi_def, e.apply_symm_apply]
      rw [QuotientGroup.eq] at hcoset
      simpa [inv_inv] using hcoset
    refine ⟨⟨(r i) * g, hmem⟩, ?_⟩
    show ((r i) * g) • τ ∈ T
    rw [mul_smul]
    exact Set.mem_iUnion.mpr ⟨i, Set.smul_mem_smul_set hg⟩
  · intro h₁ h₂ hne
    show AEDisjoint μ ((h₁ : G) • T) ((h₂ : G) • T)
    rw [hT_def]
    simp only [Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff,
      ← mul_smul]
    exact fun i₁ i₂ ↦ hs.aedisjoint fun heq ↦ hne (eq_of_mul_transversal hinj heq).1


/-- **Conjugation-shift of a fundamental domain.** If `s` is an `H₁`-fundamental
domain (where `H₁ ≤ G_outer`) and `H₂` is the pointwise conjugate `g · H₁ · g⁻¹`
(in `Subgroup` pointwise smul form, via the `ConjAct G_outer`-action), then
`g • s` is an `H₂`-fundamental domain. -/
theorem fundamentalDomain_smul_of_eq_conjAct
    {G_outer α : Type*} [Group G_outer] [MeasurableSpace α] [MulAction G_outer α]
    [MeasurableConstSMul G_outer α] {μ : Measure α} [SMulInvariantMeasure G_outer α μ]
    {H₁ H₂ : Subgroup G_outer} {s : Set α} (hs : IsFundamentalDomain H₁ s μ)
    {g : G_outer} (hgH : H₂ = ConjAct.toConjAct g • H₁) :
    IsFundamentalDomain H₂ (g • s) μ := by
  subst hgH
  refine hs.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul _ _).quasiMeasurePreserving
    { toFun := fun h₂ ↦ ⟨g⁻¹ * (h₂ : G_outer) * g, ?_⟩
      invFun := fun h₁ ↦ ⟨g * (h₁ : G_outer) * g⁻¹, ?_⟩
      left_inv := fun _ ↦ Subtype.ext (by group)
      right_inv := fun _ ↦ Subtype.ext (by group) } fun h₂ x ↦ ?_
  · have := h₂.2
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at this
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
      show g⁻¹ * (g * (h₁ : G_outer) * g⁻¹) * g = (h₁ : G_outer) from by group]
    exact h₁.2
  · show g • ((g⁻¹ * (h₂ : G_outer) * g) • x) = (h₂ : G_outer) • (g • x)
    simp only [smul_smul, mul_inv_cancel_left, mul_assoc]

/-- **AE-disjointness of arbitrary `G_outer`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G_outer` acting on `α` with a
`G_outer`-invariant measure `μ`. For any pair `g₁, g₂ ∈ G_outer` whose relative
position `g₁⁻¹ * g₂` lies in `H` and is non-trivial, the translates `g₁ • D` and
`g₂ • D` are `AE`-disjoint with respect to `μ`. -/
theorem fundamentalDomain_aedisjoint_smul_of_mul_inv_mem
    {G_outer α : Type*} [Group G_outer] [MeasurableSpace α] [MulAction G_outer α]
    {μ : Measure α} [SMulInvariantMeasure G_outer α μ]
    {H : Subgroup G_outer} {D : Set α} (hD : IsFundamentalDomain H D μ)
    {g₁ g₂ : G_outer} (h_mem : g₁⁻¹ * g₂ ∈ H) (h_ne : g₁⁻¹ * g₂ ≠ 1) :
    AEDisjoint μ (g₁ • D) (g₂ • D) := by
  have h_core : AEDisjoint μ ((1 : H) • D) ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D) :=
    hD.aedisjoint fun heq ↦ h_ne <| by
      simpa [Subgroup.coe_one, eq_comm] using congr_arg (Subtype.val : H → G_outer) heq
  rw [one_smul, show ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D : Set α) = (g₁⁻¹ * g₂) • D from rfl]
    at h_core
  show μ ((g₁ • D) ∩ (g₂ • D)) = 0
  rw [show (g₁ • D) ∩ (g₂ • D) = g₁ • (D ∩ ((g₁⁻¹ * g₂) • D)) from by
      rw [Set.smul_set_inter, ← mul_smul, mul_inv_cancel_left], measure_smul]
  exact h_core


end
end Dubon2026

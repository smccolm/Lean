/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The final adjunction calculation adapts P2M/Sol/
S_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv.lean at revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Acyclicity and the connecting
isomorphism reuse the pinned Shapiro theorem and original native free cover.
-/
import Dubon2026.OriginalInducedFiniteCoefficientSequence
import Dubon2026.OriginalFiniteRelationAcyclicity

/-! # The actual induced relation connecting map is an isomorphism

For DUB-17's middle-extension step, the existing free-cover acyclicity
and pinned induction/coinduction isomorphism make the actual connecting
map invertible. The already proved injective class trace can then detect
the restricted H2 map directly, avoiding a new connecting/trace square.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (N : Subgroup G) (B : Rep.{0} ℤ G) [Finite B]

/-- The actual induced subgroup free cover has zero positive cohomology. -/
theorem originalInducedRelationFree_positive_zero (n : ℕ) :
    Limits.IsZero (groupCohomology
      (Rep.ind N.subtype (Rep.free ℤ N (Rep.res N.subtype B))) (n + 1)) := by
  classical
  let A := Rep.free ℤ N (Rep.res N.subtype B)
  exact (originalRelationFreeCover_positive_zero (Rep.res N.subtype B) n).of_iso
    (((groupCohomology.functor ℤ G (n + 1)).mapIso (Rep.indCoindIso A)) ≪≫
      groupCohomology.coindIso A (n + 1))

/-- The genuine induced relation connecting map is an isomorphism. -/
theorem originalInducedRelationConnecting_isIso :
    IsIso (groupCohomology.δ (originalInducedRelationSequence_shortExact N B) 1 2 rfl) :=
  groupCohomology.isIso_δ_of_isZero (originalInducedRelationSequence_shortExact N B) 1
    (originalInducedRelationFree_positive_zero N B 0)
    (originalInducedRelationFree_positive_zero N B 1)

omit [Finite G] [Finite B] in
/-- The actual induction adjunction transports extension through the
subgroup's original free cover to extension through its induced cover. -/
theorem originalInducedRelation_extension_iff (C : Rep.{0} ℤ G)
    (φ : Rep.ind N.subtype (originalRelationModule (Rep.res N.subtype B)) ⟶ C) :
    (∃ χ : Rep.ind N.subtype (Rep.free ℤ N (Rep.res N.subtype B)) ⟶ C,
      (Rep.indFunctor ℤ N.subtype).map (originalRelationInclusion (Rep.res N.subtype B)) ≫ χ = φ) ↔
    ∃ χ₀ : Rep.free ℤ N (Rep.res N.subtype B) ⟶ Rep.res N.subtype C,
      originalRelationInclusion (Rep.res N.subtype B) ≫ χ₀ =
        (Rep.indResAdjunction ℤ N.subtype).homEquiv _ C φ := by
  constructor
  · rintro ⟨χ, rfl⟩
    exact ⟨(Rep.indResAdjunction ℤ N.subtype).homEquiv _ C χ,
      ((Rep.indResAdjunction ℤ N.subtype).homEquiv_naturality_left _ χ).symm⟩
  · rintro ⟨χ₀, h⟩
    refine ⟨((Rep.indResAdjunction ℤ N.subtype).homEquiv _ C).symm χ₀, ?_⟩
    apply ((Rep.indResAdjunction ℤ N.subtype).homEquiv _ C).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, h]

end
end Dubon2026

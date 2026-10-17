import Dubon2026.OriginalInvariantAbelianTrace

/-! # Subgroup norm adjustments preserve the actual abelianization image

The literal norm tower removes the correction used to make an inertia
invariant integral. This supplies the exact norm-class identity in
DUB-17's local inertia to outside-unit comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0} ℤ G)
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- Adjusting by a literal subgroup norm changes the relative trace by
the literal full-group norm. -/
theorem originalInvariantRelativeTrace_sub_norm
    (x : C.quotientToInvariants S) (b : C) :
    originalInvariantRelativeTrace C S (x - originalSubgroupNormToInvariants C S b) =
      originalInvariantRelativeTrace C S x - originalInvariantNormLinear C b := by
  apply Subtype.ext
  change ((C.quotientToInvariants S).ρ.norm
    (x - originalSubgroupNormToInvariants C S b)).val = _
  rw [map_sub, Submodule.coe_sub, originalRepresentation_norm_tower]
  rfl

/-- A subgroup norm adjustment leaves the actual invariant
abelianization class of its relative trace unchanged. -/
theorem originalInvariantAbelianMap_trace_sub_norm
    (φ : groupCohomology.cocycles₂ C) (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ T : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 2))
    (x : C.quotientToInvariants S) (b : C) :
    originalInvariantAbelianMap C φ p hG h
      (originalInvariantRelativeTrace C S (x - originalSubgroupNormToInvariants C S b)) =
    originalInvariantAbelianMap C φ p hG h (originalInvariantRelativeTrace C S x) := by
  rw [originalInvariantRelativeTrace_sub_norm, map_sub]
  have hz := (originalInvariantAbelianMap_eq_zero_iff C φ p hG h
    (originalInvariantNormLinear C b)).mpr ⟨b, rfl⟩
  rw [hz, sub_zero]

end
end Dubon2026

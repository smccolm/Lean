import Dubon2026.ResidualRelationQuotient

/-! The simultaneous original inertia relations define one genuine
local coefficient quotient. This is the quotient whose coefficient
maps will be compared with original-support deformation fibers in the
Dubon Theorem 2.6 augmentation specialization. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {S ι O R : Type*} {G : S → Type*} [∀ s, Group (G s)]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

omit [IsLocalRing R] in
/-- A coefficient map kills the sum of the original subgroup relation
ideals precisely when all the original subgroup matrices become one. -/
theorem matrixFamilyRelationIdeal_le_kernel_iff
    (ρ : ∀ s, G s →* GeneralLinearGroup ι R) (I : ∀ s, Subgroup (G s))
    {A : Type*} [CommRing A] (f : R →+* A) :
    (⨆ s, matrixRepresentationRelationIdeal (ρ s) (I s)) ≤ RingHom.ker f ↔
      ∀ s g, g ∈ I s → GeneralLinearGroup.map f (ρ s g) = 1 := by
  rw [iSup_le_iff]
  apply forall_congr'
  intro s
  exact matrixRepresentationRelationIdeal_le_kernel_iff (ρ s) (I s) f

/-- Residual triviality of all the original subgroup actions makes
their simultaneous quotient nontrivial and local. -/
theorem matrixFamilyRelationQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : ∀ s, G s →* GeneralLinearGroup ι R) (I : ∀ s, Subgroup (G s))
    (hres : ∀ s g, g ∈ I s →
      GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom (ρ s g) = 1) :
    IsLocalRing (R ⧸ ⨆ s, matrixRepresentationRelationIdeal (ρ s) (I s)) := by
  let J := ⨆ s, matrixRepresentationRelationIdeal (ρ s) (I s)
  have hk := (matrixFamilyRelationIdeal_le_kernel_iff ρ I (localCoefficientReduction eR).toRingHom).mpr hres
  have hm : J ≤ IsLocalRing.maximalIdeal R := fun r hr =>
    (localCoefficientReduction_eq_zero_iff eR r).mp (hk hr)
  have hj : J ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hm
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hj
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

end
end Dubon2026

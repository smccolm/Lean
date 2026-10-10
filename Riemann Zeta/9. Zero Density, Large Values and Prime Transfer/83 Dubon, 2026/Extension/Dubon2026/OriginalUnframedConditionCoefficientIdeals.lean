import Dubon2026.OriginalUnframedDeterminantInertiaConditions
import Dubon2026.OriginalCoefficientRepresentationClass
import Dubon2026.RepresentationDeterminantIdeal

/-! # Actual original unframed conditions are exactly the existing genuine coefficient ideal conditions -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Evaluating the actual original whole trace representation satisfies the prescribed unframed determinant exactly when the same original coefficient map kills the existing literal determinant ideal. -/
theorem originalUnframedDeterminant_coefficient_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedHasDeterminant eA H σ δ
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ≤ RingHom.ker f.val.toRingHom := by
  exact (representationDeterminantIdeal_le_kernel_iff τ.toMonoidHom δ f.val).symm

/-- Evaluating the actual original whole trace representation kills the genuine original subgroup exactly when the same original coefficient map kills the existing literal matrix-relation ideal. -/
theorem originalUnframedSubgroup_coefficient_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (N : Subgroup H) (f : OriginalContinuousCoefficientFiber eR eA) :
    originalUnframedKillsSubgroup eA H σ N
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ↔
      matrixRepresentationRelationIdeal τ.toMonoidHom N ≤ RingHom.ker f.val.toRingHom := by
  exact (matrixRepresentationRelationIdeal_le_kernel_iff τ.toMonoidHom N f.val.toRingHom).symm

/-- The actual original unframed fixed-determinant and original subgroup conditions together are exactly annihilation of the sum of the two existing genuine original coefficient ideals. -/
theorem originalUnframedDeterminantSubgroup_coefficient_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H) (f : OriginalContinuousCoefficientFiber eR eA) :
    (originalUnframedHasDeterminant eA H σ δ
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ∧
      originalUnframedKillsSubgroup eA H σ N
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f)) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixRepresentationRelationIdeal τ.toMonoidHom N ≤ RingHom.ker f.val.toRingHom := by
  rw [originalUnframedDeterminant_coefficient_iff eR eA H σ τ hτ δ f,
    originalUnframedSubgroup_coefficient_iff eR eA H σ τ hτ N f, sup_le_iff]

end
end Dubon2026

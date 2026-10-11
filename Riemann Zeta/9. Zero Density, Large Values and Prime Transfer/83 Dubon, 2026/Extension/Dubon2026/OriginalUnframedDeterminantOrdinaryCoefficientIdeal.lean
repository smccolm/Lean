import Dubon2026.OriginalUnframedConditionCoefficientIdeals
import Dubon2026.OriginalUnframedOrdinaryCoefficientIdeal

/-! # The literal simultaneous determinant and ordinary ideal on original classes -/

namespace Dubon2026
noncomputable section
open Matrix

variable {O R A : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The original prescribed determinant and genuine ordinary condition hold together exactly when the same coefficient map kills the sum of their literal original coefficient ideals. -/
theorem originalUnframedDeterminantOrdinary_coefficient_iff
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup (Fin 2) R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    (f : OriginalContinuousCoefficientFiber eR eA) :
    (originalUnframedHasDeterminant eA H σ δ
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f) ∧
      originalUnframedOrdinary eA H σ N
        (originalCoefficientRepresentationClass eR eA H σ τ hτ f)) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀ ≤
          RingHom.ker f.val.toRingHom := by
  rw [originalUnframedDeterminant_coefficient_iff eR eA H σ τ hτ δ f,
    originalUnframedOrdinary_coefficient_iff eR eA H σ τ hτ N g₀ hg₀ f, sup_le_iff]

end
end Dubon2026

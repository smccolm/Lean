import Dubon2026.OriginalUnframedDeterminantOrdinaryCoefficientIdeal
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The literal determinant and ordinary quotient classifies the genuine original classes with determinant and ordinary conditions -/

namespace Dubon2026
noncomputable section
open Matrix

variable {O R A : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The same original universal class map restricts along the literal determinant and ordinary coefficient quotient to classify exactly the actual original fixed-determinant ordinary invariant-summand classes. -/
def originalUnframedDeterminantOrdinaryQuotientEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup (Fin 2) R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    [IsLocalRing (R ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ)) :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR
      ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀))) eA ≃
      {c : OriginalUnframedDeformationClass eA H σ // originalUnframedHasDeterminant eA H σ δ c ∧ originalUnframedOrdinary eA H σ N c} := by
  let J := (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀)
  let e := Equiv.ofBijective (originalCoefficientRepresentationClass eR eA H σ τ hτ) hbij
  exact (originalLocalQuotientCoefficientFiberEquiv eR eA J).trans
    (e.subtypeEquiv (fun f =>
      (originalUnframedDeterminantOrdinary_coefficient_iff eR eA H σ τ hτ δ N g₀ hg₀ f).symm))

/-- The combined determinant and ordinary quotient equivalence evaluates the original universal matrices through the same original quotient coefficient map. -/
theorem originalUnframedDeterminantOrdinaryQuotientEquiv_evaluation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{0}) (σ : H →* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup (Fin 2) R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H) (g₀ : N) (hg₀ : σ g₀.val ≠ 1)
    [IsLocalRing (R ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR
      ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀))) eA) :
    (originalUnframedDeterminantOrdinaryQuotientEquiv eR eA H σ τ hτ δ N g₀ hg₀ hbij f).val =
      originalCoefficientRepresentationClass eR eA H σ τ hτ
        (originalQuotientCoefficientRestriction eR eA
          ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixOrdinaryRelationIdeal (τ.toMonoidHom.comp N.subtype) g₀)) f).val := by
  rfl

end
end Dubon2026

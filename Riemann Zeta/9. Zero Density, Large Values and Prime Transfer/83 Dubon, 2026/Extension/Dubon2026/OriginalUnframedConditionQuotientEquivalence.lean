import Dubon2026.OriginalUnframedConditionCoefficientIdeals
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The actual original coefficient quotient classifies determinant and subgroup conditions -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Restrict the proved genuine original class classification to determinant and original subgroup conditions, using the existing actual quotient coefficient equivalence and the literal sum of original relation ideals. -/
def originalUnframedConditionQuotientEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H)
    [IsLocalRing (R ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixRepresentationRelationIdeal τ.toMonoidHom N))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ)) :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR
      (representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixRepresentationRelationIdeal τ.toMonoidHom N)) eA ≃
      {c : OriginalUnframedDeformationClass eA H σ //
        originalUnframedHasDeterminant eA H σ δ c ∧ originalUnframedKillsSubgroup eA H σ N c} := by
  let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
    matrixRepresentationRelationIdeal τ.toMonoidHom N
  let e := Equiv.ofBijective (originalCoefficientRepresentationClass eR eA H σ τ hτ) hbij
  exact (originalLocalQuotientCoefficientFiberEquiv eR eA J).trans
    (e.subtypeEquiv (fun f =>
      (originalUnframedDeterminantSubgroup_coefficient_iff eR eA H σ τ hτ δ N f).symm))

/-- The genuine quotient classification maps each original quotient coefficient morphism to the class of the original universal matrices evaluated through that same morphism and the literal quotient map. -/
theorem originalUnframedConditionQuotientEquiv_evaluation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι R)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ)
    (δ : H →* Oˣ) (N : Subgroup H)
    [IsLocalRing (R ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔
      matrixRepresentationRelationIdeal τ.toMonoidHom N))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR
      (representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixRepresentationRelationIdeal τ.toMonoidHom N)) eA) :
    (originalUnframedConditionQuotientEquiv eR eA H σ τ hτ δ N hbij f).val =
      originalCoefficientRepresentationClass eR eA H σ τ hτ
        (originalQuotientCoefficientRestriction eR eA
          (representationDeterminantIdeal τ.toMonoidHom δ ⊔
            matrixRepresentationRelationIdeal τ.toMonoidHom N) f).val := by
  rfl

end
end Dubon2026

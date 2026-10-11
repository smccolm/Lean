import Dubon2026.OriginalUnframedDeterminantFiniteFlatCoefficientIdeal
import Dubon2026.MatrixHopfModelCoefficientIdealLocal
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The genuine quotient for the simultaneous determinant and geometric finite-flat condition -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B] [T2Space B]

/-- Restrict the original coefficient classification by the simultaneous prescribed
determinant and geometric finite-flat conditions. The proved kernel criterion identifies
this precise subfamily with maps out of the literal sum of the two original ideals. -/
def originalUnframedDeterminantFiniteFlatQuotientEquiv
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (δ : H →* Oˣ)
    [IsLocalRing (A ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))) eB ≃
      {c : OriginalUnframedDeformationClass eB H σ //
        originalUnframedHasDeterminant eB H σ δ c ∧
          originalUnframedFiniteFlatScheme R F K eB H σ j c} := by
  let J := (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))
  let e := Equiv.ofBijective (originalCoefficientRepresentationClass eA eB H σ τ hτ) hbij
  exact (originalLocalQuotientCoefficientFiberEquiv eA eB J).trans
    (e.subtypeEquiv (fun f =>
      (originalUnframedDeterminantFiniteFlat_coefficient_iff hB eA eB H σ τ hτ j I₀ hI₀ m₀ δ f).symm))

/-- The genuine quotient classification evaluates the same original representation through
the actual quotient coefficient map, preserving its original class rather than a new surrogate. -/
theorem originalUnframedDeterminantFiniteFlatQuotientEquiv_evaluation
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (j : (K ≃ₐ[F] K) →* H)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ (τ.toMonoidHom.comp j))))
    (δ : H →* Oˣ)
    [IsLocalRing (A ⧸ (representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)))) eB) :
    (originalUnframedDeterminantFiniteFlatQuotientEquiv hB eA eB H σ τ hτ j I₀ hI₀ m₀ δ hbij f).val =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB
          ((representationDeterminantIdeal τ.toMonoidHom δ ⊔ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) f).val := by
  rfl

end
end Dubon2026

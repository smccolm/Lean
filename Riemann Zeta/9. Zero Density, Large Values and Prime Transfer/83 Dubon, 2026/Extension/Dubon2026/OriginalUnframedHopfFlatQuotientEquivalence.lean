import Dubon2026.OriginalUnframedHopfFlatCoefficientIdeal
import Dubon2026.MatrixHopfModelCoefficientIdealLocal
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The actual model coefficient quotient classifies the original local model condition

The unrestricted original class bijection is an explicit upstream input. The local
condition is derived by the proved kernel characterization of the actual model ideal.
No universal arithmetic representation or residual model is asserted here.
-/

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

/-- Restrict the original unrestricted coefficient classification to the actual all-adic
local model condition. The original quotient coefficient equivalence uses the literal
model ideal, and the local-condition kernel theorem proves exactly the required restriction. -/
def originalUnframedHopfFlatQuotientEquiv
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
    [IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) eB ≃
      {c : OriginalUnframedDeformationClass eB H σ //
        originalUnframedHopfFlat R F K eB H σ j c} := by
  let J := matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)
  let e := Equiv.ofBijective (originalCoefficientRepresentationClass eA eB H σ τ hτ) hbij
  exact (originalLocalQuotientCoefficientFiberEquiv eA eB J).trans
    (e.subtypeEquiv (fun f =>
      (originalUnframedHopfFlat_coefficient_iff hB eA eB H σ τ hτ j I₀ hI₀ m₀ f).symm))

/-- The genuine quotient classification evaluates the same original representation through
the actual quotient coefficient map, preserving its original class rather than a new surrogate. -/
theorem originalUnframedHopfFlatQuotientEquiv_evaluation
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
    [IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))]
    (hbij : Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ))
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA
      (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j))) eB) :
    (originalUnframedHopfFlatQuotientEquiv hB eA eB H σ τ hτ j I₀ hI₀ m₀ hbij f).val =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB
          (matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j)) f).val := by
  rfl

end
end Dubon2026

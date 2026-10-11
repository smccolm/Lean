import Dubon2026.OriginalUnframedHopfFlatCoefficientIdeal
import Dubon2026.OriginalUnframedFiniteFlatSchemeCondition
import Dubon2026.OriginalUnframedConditionCoefficientIdeals

/-! # The actual simultaneous determinant and geometric finite-flat coefficient ideal -/

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

/-- The same original evaluated class satisfies its prescribed determinant and actual
geometric finite-flat condition at every positive adic level exactly when its original
coefficient map kills the sum of the genuine determinant and model ideals. -/
theorem originalUnframedDeterminantFiniteFlat_coefficient_iff
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
    (δ : H →* Oˣ) (f : OriginalContinuousCoefficientFiber eA eB) :
    (originalUnframedHasDeterminant eB H σ δ
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f) ∧
      originalUnframedFiniteFlatScheme R F K eB H σ j
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f)) ↔
      representationDeterminantIdeal τ.toMonoidHom δ ⊔
        matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j) ≤
        RingHom.ker f.val.toRingHom := by
  rw [← originalUnframedHopfFlat_iff_finiteFlatScheme eB H σ j,
    originalUnframedDeterminant_coefficient_iff eA eB H σ τ hτ δ f,
    originalUnframedHopfFlat_coefficient_iff hB eA eB H σ τ hτ j I₀ hI₀ m₀ f,
    sup_le_iff]

end
end Dubon2026

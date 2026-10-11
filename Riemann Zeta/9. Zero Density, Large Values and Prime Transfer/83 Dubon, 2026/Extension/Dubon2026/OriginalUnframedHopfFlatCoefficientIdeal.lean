import Dubon2026.OriginalUnframedHopfFlatCondition
import Dubon2026.MatrixHopfModelCoefficientKernel
import Dubon2026.OriginalCoefficientRepresentationClass

/-! # The original unframed local model condition equals the genuine coefficient-kernel condition -/

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

/-- The actual original unframed class obtained by the existing continuous residue-preserving coefficient evaluation has the entire local model condition exactly when that same original coefficient map kills the literal closed model ideal of the same original restricted representation. -/
theorem originalUnframedHopfFlat_coefficient_iff
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
    (f : OriginalContinuousCoefficientFiber eA eB) :
    originalUnframedHopfFlat R F K eB H σ j
        (originalCoefficientRepresentationClass eA eB H σ τ hτ f) ↔
      matrixHopfModelCoefficientIdeal R F K (τ.toMonoidHom.comp j) ≤
        RingHom.ker f.val.toRingHom := by
  letI : Finite (IsLocalRing.ResidueField B) := Finite.of_injective eB eB.injective
  change MatrixAdicHopfFlat R F K
      ((GeneralLinearGroup.map f.val.toRingHom).comp (τ.toMonoidHom.comp j)) ↔ _
  exact matrixAdicHopfFlat_coefficient_iff_modelIdeal_le_ker hB
    (τ.toMonoidHom.comp j) I₀ hI₀ m₀ f.val.toRingHom f.property.1

end
end Dubon2026

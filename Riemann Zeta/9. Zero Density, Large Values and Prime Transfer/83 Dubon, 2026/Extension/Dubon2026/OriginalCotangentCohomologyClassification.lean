import Dubon2026.OriginalCotangentCohomologyClass
import Dubon2026.FiniteNilpotentAdicCoefficients

/-! # Original coefficient-class universality gives genuine cotangent/cohomology classification -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [IsTopologicalRing A] in
/-- Injectivity of the original coefficient-to-unframed-class map makes the actual
linear cotangent class map injective. The proof uses the true dual-number point
equivalence and the exact original continuous cohomology comparison. -/
private theorem originalCotangentCohomologyClassLinearMap_injective
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (hinj : letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
      Function.Injective (originalCoefficientRepresentationClass eA
        (relativeDualNumberResidueEquiv O) H σ τ hτ)) :
    Function.Injective (originalCotangentCohomologyClassLinearMap hA eA H σ hσ τ hτ) := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  intro d e h
  apply (originalResidueCotangentContinuousFiberEquiv hA eA).injective
  apply hinj
  apply (relativeDualNumberUnframedCohomologyMap_bijective H σ hσ).1
  exact (originalCotangentCohomologyClassLinearMap_coefficient hA eA H σ hσ τ hτ d).symm.trans
    (h.trans (originalCotangentCohomologyClassLinearMap_coefficient hA eA H σ hσ τ hτ e))

omit [IsTopologicalRing A] in
/-- Proved original coefficient-class universality for all complete Noetherian targets
yields a genuine residue-field-linear
cotangent classification of the entire original continuous adjoint cohomology. This
consumes full original representation universality, specializing it to the derived
complete finite dual-number target before applying the original point comparison. -/
theorem originalCotangentCohomologyClassLinearMap_bijective
    [Finite (IsLocalRing.ResidueField O)]
    (hA : (inferInstance : TopologicalSpace A) = (IsLocalRing.maximalIdeal A).adicTopology)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (hbij : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
      (_hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
      (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eA eB H σ τ hτ)) :
    Function.Bijective (originalCotangentCohomologyClassLinearMap hA eA H σ hσ τ hτ) := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  have hdual := hbij (DualNumber (IsLocalRing.ResidueField O)) rfl
    (relativeDualNumberResidueEquiv O)
  refine ⟨originalCotangentCohomologyClassLinearMap_injective hA eA H σ hσ τ hτ hdual.1, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := (relativeDualNumberUnframedCohomologyMap_bijective H σ hσ).2 x
  obtain ⟨f, hf⟩ := hdual.2 c
  obtain ⟨d, hd⟩ := (originalResidueCotangentContinuousFiberEquiv hA eA).surjective f
  refine ⟨d, ?_⟩
  rw [originalCotangentCohomologyClassLinearMap_coefficient, hd, hf]
  exact hc

end
end Dubon2026

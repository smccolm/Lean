import Dubon2026.OriginalResidueDerivationMatrices
import Dubon2026.OriginalRelativeCoefficientFiberEquiv
import Dubon2026.DualNumberAdicTopology
import Dubon2026.ContinuousAdjointCohomology

/-! # Genuine continuity and linearity of original relative residue cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [IsTopologicalRing R] in
/-- Evaluating a genuine original relative residue derivation on the original continuous representation gives a continuous first-order lift in the actual product topology. -/
theorem originalResidueDerivationFirstOrderLift_continuous
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) :
    Continuous (originalResidueDerivationFirstOrderLift eR ρ σ hres d).val := by
  let K := IsLocalRing.ResidueField O
  letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
  letI : TopologicalSpace (DualNumber K) := (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
  let f := originalResidueDerivationContinuousFiberEquiv hR eR d
  have hf : Continuous (GeneralLinearGroup.map (n := ι) f.val.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact f.property.1.comp (continuous_apply_apply i j)
  exact (dualNumberGL_continuous_iff K _).mp (hf.comp hρ)

/-- The actual relative residue cocycle map is linear over the original residue field and lands in genuine continuous cocycles. -/
def originalResidueDerivationContinuousCocycleLinearMap
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    OriginalResidueDerivations eR →ₗ[IsLocalRing.ResidueField O] continuousMatrixAdjointCocycles σ where
  toFun d := ⟨originalResidueDerivationCocycleLinearMap eR ρ σ hres d,
    matrixFirstOrderCocycle_continuous σ hσ (originalResidueDerivationFirstOrderLift eR ρ σ hres d)
      (originalResidueDerivationFirstOrderLift_continuous hR eR ρ hρ σ hres d)⟩
  map_add' d e := by
    apply Subtype.ext
    exact map_add (originalResidueDerivationCocycleLinearMap eR ρ σ hres) d e
  map_smul' a d := by
    apply Subtype.ext
    exact map_smul (originalResidueDerivationCocycleLinearMap eR ρ σ hres) a d

omit [IsTopologicalRing R] in
/-- The actual continuous relative residue cocycle retains every original right-logarithmic matrix value. -/
theorem originalResidueDerivationContinuousCocycleLinearMap_apply
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) (g : G) :
    (originalResidueDerivationContinuousCocycleLinearMap hR eR ρ hρ σ hσ hres d).val g =
      originalResidueDerivationMatrix eR ρ d g * ((σ g)⁻¹).val :=
  originalResidueDerivationFirstOrderLift_cocycle eR ρ σ hres d g

end
end Dubon2026

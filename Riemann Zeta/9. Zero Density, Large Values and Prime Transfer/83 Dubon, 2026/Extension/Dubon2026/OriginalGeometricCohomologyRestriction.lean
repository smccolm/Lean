import Dubon2026.LocalGeometricFiniteFlatCohomology
import Dubon2026.OriginalGeometricFiniteFlatCohomologySubmodule
import Dubon2026.RelativeDualNumberDeterminantCohomology

/-! # The intrinsic global geometric condition is the genuine local restriction condition -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι O : Type}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The intrinsic prescribed-determinant geometric condition is exactly the actual
trace condition together with finite-flat geometric membership of the restricted
continuous cohomology class. The reverse implication uses invariance under genuine
strict conjugacy, so the local model need not be supplied for a chosen representative. -/
theorem originalGeometricFiniteFlatCohomologyCondition_restriction_iff
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (j : (K ≃ₐ[F] K) →* H) (hj : Continuous j)
    (x : ContinuousMatrixAdjointH1 σ hσ) :
    x ∈ originalGeometricFiniteFlatCohomologyCondition (R := R) H σ hσ δ j ↔
      x ∈ continuousFixedDeterminantClasses σ hσ ∧
        continuousMatrixAdjointH1Restriction σ hσ j hj x ∈
          localGeometricFiniteFlatCohomologyCondition R F K (σ.comp j) (hσ.comp hj) := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  obtain ⟨τ, rfl⟩ := continuousMatrixFirstOrderClass_surjective σ hσ x
  let c := originalUnframedClass (relativeDualNumberResidueEquiv O) H σ
    (relativeDualNumberFramedFiberEquiv H σ τ)
  have hmap : relativeDualNumberUnframedCohomologyMap H σ hσ c =
      continuousMatrixFirstOrderClass σ hσ τ.val τ.property :=
    relativeDualNumberUnframedCohomologyMap_apply H σ hσ τ
  have hclass : continuousMatrixFirstOrderClass σ hσ τ.val τ.property ∈
      originalGeometricFiniteFlatCohomologyCondition (R := R) H σ hσ δ j ↔
        originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ∧
          originalUnframedFiniteFlatScheme R F K (relativeDualNumberResidueEquiv O) H σ j c := by
    constructor
    · rintro ⟨d, hd, hx⟩
      have hdc : d = c := (relativeDualNumberUnframedCohomologyMap_bijective H σ hσ).1
        (hx.trans hmap.symm)
      rwa [hdc] at hd
    · intro hc
      exact ⟨c, hc, hmap⟩
  rw [hclass, relativeDualNumberUnframedHasDeterminant_iff H σ hσ δ hδ c,
    hmap, continuousMatrixAdjointH1Restriction_class,
    localGeometricFiniteFlatCohomologyCondition_class_iff]
  rfl

end
end Dubon2026

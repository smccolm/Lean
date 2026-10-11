import Dubon2026.RelativeDualNumberUnframedCohomologyEquiv
import Dubon2026.OriginalUnframedDeterminantInertiaConditions
import Dubon2026.ContinuousFixedDeterminantClasses

/-! # The original prescribed determinant is exactly the actual continuous trace condition -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The true original dual-number determinant condition corresponds exactly to the
existing trace-kernel submodule under the genuine original class/cohomology map.
The determinant character is only required to have the actual residual determinant. -/
theorem relativeDualNumberUnframedHasDeterminant_iff
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : H →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    ∀ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H σ,
      originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) H σ δ c ↔
        relativeDualNumberUnframedCohomologyMap H σ hσ c ∈
          continuousFixedDeterminantClasses σ hσ := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  intro c
  obtain ⟨ρ, rfl⟩ := originalUnframedClass_surjective
    (relativeDualNumberResidueEquiv O) H σ c
  obtain ⟨τ, rfl⟩ := (relativeDualNumberFramedFiberEquiv H σ).surjective ρ
  rw [relativeDualNumberUnframedCohomologyMap_apply,
    originalUnframedHasDeterminant_class_iff,
    continuousFixedDeterminantClasses_firstOrder_iff]
  apply forall_congr'
  intro g
  have hres : Matrix.det (σ g).val = IsLocalRing.residue O (δ g).val :=
    congrArg Units.val (hδ g)
  have hconst :
      (Units.map (algebraMap O (DualNumber (IsLocalRing.ResidueField O))).toMonoidHom (δ g)).val =
        TrivSqZeroExt.inl (Matrix.det (σ g).val) := by
    change algebraMap O (DualNumber (IsLocalRing.ResidueField O)) (δ g).val = _
    rw [relativeDualNumber_algebraMap, hres]
  rw [← Units.val_inj]
  change Matrix.det (τ.val.val g).val =
    (Units.map (algebraMap O (DualNumber (IsLocalRing.ResidueField O))).toMonoidHom (δ g)).val ↔ _
  rw [hconst]

end
end Dubon2026

import Dubon2026.RelativeDualNumberFramedEquiv
import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.ContinuousAdjointCohomology

/-! # Original dual-number deformation classes and genuine continuous first cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

omit [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)] in
/-- The original coefficient reduction on a dual-number invertible matrix is exactly
the genuine first-order reduction, entry by entry through the original residue equivalence. -/
theorem relativeDualNumber_generalLinear_reduction
    (U : GeneralLinearGroup ι (DualNumber (IsLocalRing.ResidueField O))) :
    GeneralLinearGroup.map (localCoefficientReduction (relativeDualNumberResidueEquiv O)).toRingHom U =
      dualMatrixReduction U := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact relativeDualNumberResidueEquiv_reduction O (U.val i j)

/-- Two original continuous first-order lifts give the same original unframed
dual-number class exactly when their genuine continuous adjoint cohomology classes
agree. The original framed comparison retains every matrix, and its residue map
retains precisely the original identity-reducing conjugators. -/
theorem relativeDualNumberFramedClass_eq_iff_cohomology
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ)
    (τ υ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val}) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ
        (relativeDualNumberFramedFiberEquiv H ρ τ) =
      originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ
        (relativeDualNumberFramedFiberEquiv H ρ υ) ↔
      continuousMatrixFirstOrderClass ρ hρ τ.val τ.property =
        continuousMatrixFirstOrderClass ρ hρ υ.val υ.property := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  rw [originalUnframedClass_eq_iff, continuousMatrixFirstOrderClass_eq_iff]
  change (∃ U, GeneralLinearGroup.map
      (localCoefficientReduction (relativeDualNumberResidueEquiv O)).toRingHom U = 1 ∧
        ∀ g, υ.val.val g = U * τ.val.val g * U⁻¹) ↔
    ∃ U, dualMatrixReduction U = 1 ∧ ∀ g, υ.val.val g = U * τ.val.val g * U⁻¹
  simp only [relativeDualNumber_generalLinear_reduction]

end
end Dubon2026

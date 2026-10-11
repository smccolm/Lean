import Dubon2026.RelativeDualNumberClassCohomology

/-! # The original unframed dual-number fiber is actual continuous adjoint cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Map the original deformation class to the continuous cohomology class of its
same original first-order matrices. Well-definedness is the proved exact comparison
of identity-reducing conjugacy and original continuous coboundaries. -/
def relativeDualNumberUnframedCohomologyMap
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) :
    (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
       ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
     OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H ρ) →
      ContinuousMatrixAdjointH1 ρ hρ := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  let e := relativeDualNumberFramedFiberEquiv H ρ
  refine Quotient.lift (fun τ =>
    continuousMatrixFirstOrderClass ρ hρ (e.symm τ).val (e.symm τ).property) ?_
  intro τ υ h
  apply (relativeDualNumberFramedClass_eq_iff_cohomology H ρ hρ
    (e.symm τ) (e.symm υ)).mp
  simpa only [e.apply_symm_apply] using
    (Quotient.sound h : originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ τ =
      originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ υ)

/-- The class map evaluates to the cohomology class of the same genuine original
continuous first-order lift, with no new representative or cocycle convention. -/
theorem relativeDualNumberUnframedCohomologyMap_apply
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) (τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val}) :
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    relativeDualNumberUnframedCohomologyMap H ρ hρ
        (originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ
          (relativeDualNumberFramedFiberEquiv H ρ τ)) =
      continuousMatrixFirstOrderClass ρ hρ τ.val τ.property := by
  let e := relativeDualNumberFramedFiberEquiv H ρ
  change continuousMatrixFirstOrderClass ρ hρ (e.symm (e τ)).val
    (e.symm (e τ)).property = _
  rw [e.symm_apply_apply]

/-- The original unframed dual-number class map is bijective onto actual continuous
adjoint first cohomology: strict conjugacy is precisely equality of cohomology classes,
and every original continuous cohomology class has an original continuous lift. -/
theorem relativeDualNumberUnframedCohomologyMap_bijective
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) :
    Function.Bijective (relativeDualNumberUnframedCohomologyMap H ρ hρ) := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  let e := relativeDualNumberFramedFiberEquiv H ρ
  constructor
  · intro c d h
    obtain ⟨τ, rfl⟩ := originalUnframedClass_surjective (relativeDualNumberResidueEquiv O) H ρ c
    obtain ⟨υ, rfl⟩ := originalUnframedClass_surjective (relativeDualNumberResidueEquiv O) H ρ d
    have hclass := (relativeDualNumberFramedClass_eq_iff_cohomology H ρ hρ
      (e.symm τ) (e.symm υ)).mpr h
    simpa only [e.apply_symm_apply] using hclass
  · intro x
    obtain ⟨τ, hτ⟩ := continuousMatrixFirstOrderClass_surjective ρ hρ x
    refine ⟨originalUnframedClass (relativeDualNumberResidueEquiv O) H ρ (e τ), ?_⟩
    exact (relativeDualNumberUnframedCohomologyMap_apply H ρ hρ τ).trans hτ

/-- The genuine equivalence between the original unframed dual-number fiber and
its actual continuous adjoint first cohomology. -/
def relativeDualNumberUnframedCohomologyEquiv
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) :
    (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
       ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
     OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) H ρ) ≃
      ContinuousMatrixAdjointH1 ρ hρ :=
  Equiv.ofBijective (relativeDualNumberUnframedCohomologyMap H ρ hρ)
    (relativeDualNumberUnframedCohomologyMap_bijective H ρ hρ)

end
end Dubon2026

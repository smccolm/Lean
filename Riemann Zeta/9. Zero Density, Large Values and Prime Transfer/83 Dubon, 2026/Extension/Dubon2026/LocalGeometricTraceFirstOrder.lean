import Dubon2026.LocalGeometricTraceCondition
import Dubon2026.ContinuousAdjointRestriction

/-! The actual global first-order representatives of a geometric trace condition.
The local finite-flat condition is pulled back along the given genuine restriction.
Its arithmetic specialization serves DUB-17's original Selmer comparison. -/
namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι k G : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [IsTopologicalRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : G →* GeneralLinearGroup ι k) (hσ : Continuous σ)
  (j : Gal(K/F) →* G) (hj : Continuous j)
  (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
    (matrixUnderlyingGroupAction (σ.comp j)))

omit [IsTopologicalGroup G] in
/-- The geometric local condition tests the same original restricted global lift. -/
theorem localGeometricTraceCondition_global_firstOrder_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ)
    (τ : MatrixFirstOrderLift σ) (hτ : Continuous τ.val)
    (hclass : continuousMatrixFirstOrderClass σ hσ τ hτ = continuousTraceZeroH1Inclusion σ hσ x) :
    continuousTraceZeroH1Restriction σ hσ j hj x ∈
        localGeometricTraceCondition (σ.comp j) (hσ.comp hj) m ↔
      MatrixAdicFiniteFlatScheme R F K (τ.val.comp j) := by
  rw [localGeometricTraceCondition_mem_iff,
    continuousTraceZeroH1Restriction_inclusion σ hσ j hj x, ← hclass,
    continuousMatrixAdjointH1Restriction_class,
    localGeometricFiniteFlatCohomologyCondition_class_iff]
  rfl

/-- The original trace-zero restriction condition is equivalent to an actual
continuous global fixed-determinant first-order lift with the genuine local model. -/
theorem localGeometricTraceCondition_global_exists_lift_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    continuousTraceZeroH1Restriction σ hσ j hj x ∈
        localGeometricTraceCondition (σ.comp j) (hσ.comp hj) m ↔
    ∃ τ : MatrixFirstOrderLift σ, ∃ hτ : Continuous τ.val,
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (σ g).val)) ∧
      MatrixAdicFiniteFlatScheme R F K (τ.val.comp j) ∧
      continuousMatrixFirstOrderClass σ hσ τ hτ = continuousTraceZeroH1Inclusion σ hσ x := by
  constructor
  · intro hx
    obtain ⟨τ, hclass⟩ := continuousMatrixFirstOrderClass_surjective σ hσ
      (continuousTraceZeroH1Inclusion σ hσ x)
    have hc : continuousMatrixFirstOrderClass σ hσ τ.val τ.property =
        continuousTraceZeroH1Inclusion σ hσ x := hclass
    refine ⟨τ.val, τ.property, ?_, ?_, hc⟩
    · apply (continuousFixedDeterminantClasses_firstOrder_iff σ hσ τ.val τ.property).mp
      rw [hc]
      exact continuousTraceZeroH1Inclusion_mem σ hσ x
    · exact (localGeometricTraceCondition_global_firstOrder_iff
        σ hσ j hj m x τ.val τ.property hc).mp hx
  · rintro ⟨τ, hτ, _hdet, hflat, hclass⟩
    exact (localGeometricTraceCondition_global_firstOrder_iff
      σ hσ j hj m x τ hτ hclass).mpr hflat

end
end Dubon2026

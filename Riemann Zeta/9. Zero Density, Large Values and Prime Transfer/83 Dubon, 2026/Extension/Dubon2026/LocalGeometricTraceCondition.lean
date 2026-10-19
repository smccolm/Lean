import Dubon2026.LocalGeometricFiniteFlatLinearity
import Dubon2026.ContinuousTraceZeroRestriction

/-! The original trace-zero local finite-flat condition, using the proved
geometric linear closure. This supplies the actual prime-local condition in
DUB-17's Selmer comparison, with a genuine residual model retained as input. -/
namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : Gal(K/F) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
    (matrixUnderlyingGroupAction ρ))

/-- The geometric local subspace pulled back along the original trace-zero inclusion. -/
def localGeometricTraceCondition : Submodule k (ContinuousTraceZeroAdjointH1 ρ hρ) :=
  (localGeometricFiniteFlatCohomologySubmodule ρ hρ m).comap
    (continuousTraceZeroH1Inclusion ρ hρ)

/-- Membership retains the genuine geometric condition on the same included class. -/
theorem localGeometricTraceCondition_mem_iff (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    x ∈ localGeometricTraceCondition ρ hρ m ↔
      continuousTraceZeroH1Inclusion ρ hρ x ∈
        localGeometricFiniteFlatCohomologyCondition R F K ρ hρ := Iff.rfl

/-- Every actual local trace-zero finite-flat class has a genuine continuous
first-order representative whose determinant is the constant residual determinant. -/
theorem localGeometricTraceCondition_exists_lift
    (x : ContinuousTraceZeroAdjointH1 ρ hρ) (hx : x ∈ localGeometricTraceCondition ρ hρ m) :
    ∃ τ : MatrixFirstOrderLift ρ, ∃ hτ : Continuous τ.val,
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
      MatrixAdicFiniteFlatScheme R F K τ.val ∧
      continuousMatrixFirstOrderClass ρ hρ τ hτ = continuousTraceZeroH1Inclusion ρ hρ x := by
  obtain ⟨τ, hτ, hflat, hclass⟩ := (localGeometricTraceCondition_mem_iff ρ hρ m x).mp hx
  refine ⟨τ, hτ, ?_, hflat, hclass⟩
  apply (continuousFixedDeterminantClasses_firstOrder_iff ρ hρ τ hτ).mp
  rw [hclass]
  exact continuousTraceZeroH1Inclusion_mem ρ hρ x

end
end Dubon2026

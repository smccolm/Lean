import Dubon2026.MatrixAdicFiniteFlatSchemeCondition
import Dubon2026.ContinuousAdjointRestriction
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DualNumber

/-! # Genuine geometric finite-flat classes in local continuous adjoint cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

variable (R F K : Type) {ι k : Type}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- The genuine local geometric condition: a class admits a continuous first-order
representative whose actual adic reductions have finite flat group-scheme models.
This set definition does not assume linear closure or a numerical dimension. -/
def localGeometricFiniteFlatCohomologyCondition
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ) :
    Set (ContinuousMatrixAdjointH1 ρ hρ) :=
  {x | ∃ τ : MatrixFirstOrderLift ρ, ∃ hτ : Continuous τ.val,
    MatrixAdicFiniteFlatScheme R F K τ.val ∧
      continuousMatrixFirstOrderClass ρ hρ τ hτ = x}

variable {R F K}

/-- The geometric condition is true of any actual representative exactly when it
is true of its cohomology class. Equality of original classes yields the same strict
conjugator, and genuine scheme-model transport preserves every positive adic level. -/
theorem localGeometricFiniteFlatCohomologyCondition_class_iff
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
        localGeometricFiniteFlatCohomologyCondition R F K ρ hρ ↔
      MatrixAdicFiniteFlatScheme R F K τ.val := by
  constructor
  · rintro ⟨υ, hυ, hflat, hclass⟩
    obtain ⟨U, _, hc⟩ :=
      (continuousMatrixFirstOrderClass_eq_iff ρ hρ υ τ hυ hτ).mp hclass
    exact (matrixAdicFiniteFlatScheme_conjugacy_iff υ.val τ.val U hc).mp hflat
  · intro hflat
    exact ⟨τ, hτ, hflat, rfl⟩

end
end Dubon2026

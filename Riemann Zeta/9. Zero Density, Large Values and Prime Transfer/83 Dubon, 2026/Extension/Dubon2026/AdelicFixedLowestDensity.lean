import Dubon2026.AdelicLevelFiniteSpan
import Dubon2026.ProjectionCoreDensity

/-! # The actual fixed-level algebraic core is dense in the full original lowest-weight fixed-level space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Genuine finite-level invariant finite-adelic combinations are dense in every original lowest-weight fixed-level Hilbert vector. -/
theorem adelicFixedLowest_algebraic_density {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (hk : 0 < k) :
    (adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f).topologicalClosure =
      adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f := by
  have he := @projection_stable_core_closure (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicFiniteCyclicSpan f) (adelicLevelFixedSpace f) inferInstance
    (adelicLevelFixedSpace_isClosed f) (adelicLevelProjection_finiteSpan f)
  rw [adelicFiniteCyclicSpan_closure, ← adelicRotationWeightSpace_eq_finiteClosure f hf hk] at he
  exact he

end
end Dubon2026

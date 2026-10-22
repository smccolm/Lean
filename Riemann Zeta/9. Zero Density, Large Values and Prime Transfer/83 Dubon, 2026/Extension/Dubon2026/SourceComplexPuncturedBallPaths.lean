import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic exponential -> paths avoiding finitely many poles. Native ball
homeomorphisms transport path connectedness of the punctured complex plane
to punctured coordinate balls. No explicit radial-map construction is needed.
-/
namespace Dubon2026.SourceFunctionField.OriginalExpTopology
noncomputable section
open Set Metric

theorem isPathConnected_ball_diff_singleton (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (ball c r \ {c}) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall c r
  have hsrc : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) 0
  have hs : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have ht : e.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have he0 : e 0 = c := OpenPartialHomeomorph.univBall_apply_zero c r
  have himg : e '' {0}ᶜ = ball c r \ {c} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzs : z ∈ e.source := by rw [hs]; trivial
      refine ⟨ht ▸ e.map_source hzs, ?_⟩
      intro he
      apply hz
      exact e.injOn hzs (by rw [hs]; trivial) (he.trans he0.symm)
    · rintro z ⟨hz, hzc⟩
      have hzt : z ∈ e.target := ht.symm ▸ hz
      refine ⟨e.symm z, ?_, e.right_inv hzt⟩
      intro hzero
      apply hzc
      calc z = e (e.symm z) := (e.right_inv hzt).symm
        _ = e 0 := congrArg e hzero
        _ = c := he0
  rw [← himg]
  exact hsrc.image (OpenPartialHomeomorph.continuous_univBall c r)

end
end Dubon2026.SourceFunctionField.OriginalExpTopology

import Dubon2026.LinearMapSmoothJets
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Smoothness of the actual parameterized curve derivative -/

namespace Dubon2026

noncomputable section
open scoped ContDiff

/-- Joint smoothness makes the actual curve derivative at zero smooth in all remaining parameters. -/
theorem contDiff_parameter_deriv_zero {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → ℝ → V) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun w => deriv (F w) 0) := by
  apply contDiff_infty.mpr
  intro m
  have hFm : ContDiff ℝ (m + 1) (Function.uncurry F) := by
    simpa only [Nat.cast_add, Nat.cast_one] using contDiff_infty.mp hF (m + 1)
  have hd := hFm.fderiv_succ (contDiff_const : ContDiff ℝ m (fun _ : E => (0 : ℝ)))
  have he := hd.clm_apply (contDiff_const : ContDiff ℝ m (fun _ : E => (1 : ℝ)))
  simpa only [fderiv_apply_one_eq_deriv] using he

end
end Dubon2026

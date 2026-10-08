import Dubon2026.MixedCoordinateDerivatives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exact mixed derivatives under the actual exponential parameter scaling -/

namespace Dubon2026

noncomputable section
open scoped ContDiff

/-- The genuine exponential semidirect parameter change contributes its exact first-order weight to the mixed derivative. -/
theorem mixedExpScaling_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ → ℝ → V) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (r : ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F s (Real.exp (r * s) * t)) 0) 0 =
      r • deriv (F 0) 0 + deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by
  let G := fun s : ℝ => deriv (F s) 0
  have hG : ContDiff ℝ ∞ G := contDiff_parameter_deriv_zero F hF
  have hd : HasDerivAt G (deriv G 0) 0 :=
    (((contDiff_infty.mp hG 1).differentiable (by norm_num)) 0).hasDerivAt
  have he : HasDerivAt (fun s : ℝ => Real.exp (r * s)) r 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul r).exp
  have hp := (he.smul hd).deriv
  have hr : (fun s : ℝ => deriv (fun t : ℝ => F s (Real.exp (r * s) * t)) 0) =
      fun s : ℝ => Real.exp (r * s) • G s := by
    funext s
    simpa only [mul_zero] using deriv_comp_mul_left (Real.exp (r * s)) (F s) 0
  rw [hr]
  have hm := mixedCoordinateDeriv_comm F (contDiff_infty.mp hF 2)
  change deriv G 0 = _ at hm
  simpa only [mul_zero, Real.exp_zero, one_smul, G, hm, add_comm] using hp

end
end Dubon2026

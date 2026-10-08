import Dubon2026.SmoothParameterDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Actual mixed derivatives of smooth vector-valued real parameter maps -/

namespace Dubon2026

noncomputable section
open scoped ContDiff

/-- Iterated directional derivatives of an actual twice-smooth function are its genuine second Fréchet derivative. -/
theorem mixedDirectionalDeriv_eq_fderiv {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (hF : ContDiff ℝ 2 F) (v w : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F (s • v + t • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ F) 0 v w := by
  have hi (s : ℝ) : HasDerivAt (fun t : ℝ => F (s • v + t • w))
      (fderiv ℝ F (s • v) w) 0 := by
    have hp : HasDerivAt (fun t : ℝ => s • v + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (s • v)
    exact ((hF.differentiable (by norm_num) (s • v)).hasFDerivAt).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hFd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hp : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have ho := ((hFd.differentiable (by norm_num) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0 hp (by simp)
  have he := ho.clm_apply (hasDerivAt_const (0 : ℝ) w)
  have hr : (fun s : ℝ => deriv (fun t : ℝ => F (s • v + t • w)) 0) =
      fun s : ℝ => fderiv ℝ F (s • v) w := funext (fun s => (hi s).deriv)
  rw [hr]
  simpa only [Function.comp_def, map_zero, add_zero] using he.deriv

/-- The actual two directional derivatives commute for every twice-smooth vector-valued function. -/
theorem mixedDirectionalDeriv_comm {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (hF : ContDiff ℝ 2 F) (v w : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F (s • v + t • w)) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => F (s • w + t • v)) 0) 0 := by
  rw [mixedDirectionalDeriv_eq_fderiv F hF v w, mixedDirectionalDeriv_eq_fderiv F hF w v]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

/-- The two original coordinate derivatives of a genuinely smooth two-parameter vector function commute. -/
theorem mixedCoordinateDeriv_comm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ → ℝ → V) (hF : ContDiff ℝ 2 (Function.uncurry F)) :
    deriv (fun s : ℝ => deriv (F s) 0) 0 =
      deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by
  have he := mixedDirectionalDeriv_comm (Function.uncurry F) hF (1, 0) (0, 1)
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add, Function.uncurry_apply_pair] using he

end
end Dubon2026

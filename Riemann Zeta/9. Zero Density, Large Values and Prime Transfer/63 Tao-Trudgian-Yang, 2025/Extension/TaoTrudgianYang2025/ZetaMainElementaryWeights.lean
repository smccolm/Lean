import TaoTrudgianYang2025.IntervalAmplitudeBounds

/-!
# Actual elementary factors of the Atkinson main amplitude

The smooth cutoff has uniformly bounded variation, independent of
the narrow transition width. The positive square root and logarithm
are controlled on the full physical source interval.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem intervalC1Bound_zetaBandCutoff {a b c d A B : ℝ}
    (hab : a < b) (hcd : c < d) (hAB : A ≤ B) :
    IntervalC1Bound (fun x => (zetaBandCutoff a b c d x : ℂ)) A B 2 := by
  let u : ℝ → ℝ := fun x => Real.smoothTransition ((x - a) / (b - a))
  let v : ℝ → ℝ := fun x => Real.smoothTransition ((d - x) / (d - c))
  have hu : Monotone u := Real.smoothTransition.monotone.comp
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
  have hv : Antitone v := Real.smoothTransition.monotone.comp_antitone
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_left hxy d) (sub_pos.mpr hcd).le)
  have hsu : ContDiff ℝ 1 u := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hsv : ContDiff ℝ 1 v := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hbu := intervalC1Bound_ofReal_of_deriv_nonneg hAB (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => hsu.contDiffAt (x := x))
    (fun x _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (fun _ _ => hu.deriv_nonneg)
  have hbv := intervalC1Bound_ofReal_of_deriv_nonpos hAB (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => hsv.contDiffAt (x := x))
    (fun x _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (fun _ _ => hv.deriv_nonpos)
  simpa only [u, v, zetaBandCutoff, Complex.ofReal_mul, mul_one] using hbu.mul hbv hAB

theorem intervalC1Bound_zetaDivisorBandCutoff {T G L A B : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hAB : A ≤ B) :
    IntervalC1Bound (fun x => (zetaDivisorBandCutoff T G L x : ℂ)) A B 2 := by
  have hm := zetaDivisorBandEdge_strictMono hT hG
  exact intervalC1Bound_zetaBandCutoff (hm (by linarith)) (hm (by linarith)) hAB

theorem intervalC1Bound_source_sqrt {T : ℝ} (hT : 0 < T) :
    IntervalC1Bound (fun x : ℝ => (Real.sqrt x : ℂ)) (T / 16) T (Real.sqrt T) := by
  apply intervalC1Bound_ofReal_of_deriv_nonneg (by linarith) (Real.sqrt_nonneg T)
  · intro x hx
    exact Real.contDiffAt_sqrt (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1))
  · intro x hx
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hx.2⟩
  · intro x hx
    exact Real.sqrt_monotone.deriv_nonneg

theorem mul_exp_neg_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    x * Real.exp (-Real.log x / 2) = Real.sqrt x := by
  calc
    _ = Real.exp (Real.log x + (-Real.log x / 2)) := by rw [Real.exp_add, Real.exp_log hx]
    _ = x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring
    _ = _ := by rw [Real.sqrt_eq_rpow]


theorem intervalC1Bound_source_log {T : ℝ} (hT : 16 ≤ T) :
    IntervalC1Bound (fun x : ℝ => ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ))
      (T / 16) T (Real.log T + 2 * Real.eulerMascheroniConstant) := by
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  apply intervalC1Bound_ofReal_of_deriv_nonneg (by linarith)
    (by positivity [Real.log_nonneg (show 1 ≤ T by linarith)])
  · intro x hx
    exact (Real.contDiffAt_log.mpr (ne_of_gt (by linarith [hx.1] : 0 < x))).add contDiffAt_const
  · intro x hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    exact ⟨by positivity [Real.log_nonneg hx1],
      by linarith [Real.log_le_log (by linarith : 0 < x) hx.2]⟩
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [((Real.hasDerivAt_log hx0.ne').add_const
      (2 * Real.eulerMascheroniConstant)).deriv]
    positivity

theorem sourceLogWeight_le_three_log {T : ℝ} (hlog : 1 ≤ Real.log T) :
    Real.log T + 2 * Real.eulerMascheroniConstant ≤ 3 * Real.log T := by
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

end TaoTrudgianYang2025

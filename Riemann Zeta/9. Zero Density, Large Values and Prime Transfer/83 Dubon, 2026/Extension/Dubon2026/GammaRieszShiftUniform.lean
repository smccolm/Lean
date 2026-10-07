import Dubon2026.GammaRieszContourShift

/-! # Uniform convergence after the actual Riesz Gamma contour shift -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The actual finite contour shift has a quantitative error uniform across the admissible strip. -/
theorem norm_gammaRieszVerticalCutoff_sub_le {k r x β T : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) (hT : 1 ≤ T) :
    ‖gammaRieszVerticalCutoff k r x β T - gammaRieszVerticalCutoff k r x (gammaRieszLine r) T‖ ≤
      ((β - gammaRieszLine r) * (Real.exp |Real.log x| * gammaRieszStripConstant k) / Real.pi) *
        T ^ (-(1 / 2 : ℝ)) := by
  rw [gammaRieszVerticalCutoff_sub_eq hk hr0 hx
    (by unfold gammaRieszLine; linarith : -(1 / 4 : ℝ) < gammaRieszLine r)
    hβ0 (by linarith : β < 1) (by linarith : 0 ≤ T)]
  have hp := norm_gammaRiesz_horizontal_integral_le hk hr0 hr2 hx (le_refl (gammaRieszLine r)) hβ0 hβ1
    (by rw [abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT : 1 ≤ |T|)
  have hn := norm_gammaRiesz_horizontal_integral_le hk hr0 hr2 hx (le_refl (gammaRieszLine r)) hβ0 hβ1
    (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT : 1 ≤ |-T|)
  simp only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] at hp hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ)),
    norm_mul, norm_I, one_mul]
  apply (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hn hp)) (by positivity)).trans_eq
  ring

/-- The actual shifted cutoffs converge uniformly on every compact positive interval, on every admissible line. -/
theorem tendstoUniformlyOn_gammaRieszVerticalCutoff {k r a b β : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (ha : 0 < a) (hab : a ≤ b)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) :
    TendstoUniformlyOn (fun T x : ℝ => gammaRieszVerticalCutoff k r x β T)
      (gammaRieszKernel k r) atTop (Icc a b) := by
  have hcrit : TendstoUniformlyOn
      (fun T x : ℝ => gammaRieszVerticalCutoff k r x (gammaRieszLine r) T)
      (gammaRieszKernel k r) atTop (Icc a b) :=
    tendstoUniformlyOn_gammaRieszKernel hk hr0 hr2 ha hab
  let B := (β - gammaRieszLine r) *
    (Real.exp (|Real.log a| + |Real.log b|) * gammaRieszStripConstant k) / Real.pi
  have hzero : Tendsto (fun T : ℝ => B * T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (1 : ℝ), hzero.eventually (gt_mem_nhds (half_pos hε)),
    (Metric.tendstoUniformlyOn_iff.mp hcrit) (ε / 2) (half_pos hε)] with T hT hsmall hcritT
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hlog : |Real.log x| ≤ |Real.log a| + |Real.log b| := by
    have hlo := Real.log_le_log ha hx.1
    have hhi := Real.log_le_log hx0 hx.2
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
      abs_nonneg (Real.log a), abs_nonneg (Real.log b)]
  have hbound : ‖gammaRieszVerticalCutoff k r x β T - gammaRieszVerticalCutoff k r x (gammaRieszLine r) T‖ ≤
      B * T ^ (-(1 / 2 : ℝ)) := by
    apply (norm_gammaRieszVerticalCutoff_sub_le hk hr0 hr2 hx0 hβ0 hβ1 hT).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hβ0)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlog) (Real.exp_pos _).le
  have hdist : dist (gammaRieszVerticalCutoff k r x (gammaRieszLine r) T)
      (gammaRieszVerticalCutoff k r x β T) < ε / 2 := by
    rw [dist_eq_norm, norm_sub_rev]
    exact hbound.trans_lt hsmall
  exact (dist_triangle (gammaRieszKernel k r x) (gammaRieszVerticalCutoff k r x (gammaRieszLine r) T)
    (gammaRieszVerticalCutoff k r x β T)).trans_lt (by linarith [hcritT x hx])

end
end Dubon2026

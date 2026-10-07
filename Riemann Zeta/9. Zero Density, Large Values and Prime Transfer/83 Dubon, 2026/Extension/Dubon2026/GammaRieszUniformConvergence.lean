import Dubon2026.GammaRieszTruncation

/-! # Uniform convergence of actual Riesz Gamma cutoffs on positive compact intervals -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The explicit actual tail threshold increases with the positive Mellin argument. -/
theorem gammaRieszTailHeight_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (k : ℝ) :
    gammaRieszTailHeight k x ≤ gammaRieszTailHeight k y := by
  unfold gammaRieszTailHeight
  apply max_le_max le_rfl
  apply max_le_max le_rfl
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (add_le_add (Real.log_le_log hx hxy) le_rfl) (by norm_num)

/-- The genuine normalized symmetric cutoffs converge uniformly on every closed positive interval. -/
theorem tendstoUniformlyOn_gammaRieszKernel {k r a b : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun T x : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, gammaRieszIntegrand k r x t)
      (gammaRieszKernel k r) atTop (Icc a b) := by
  have hb : 0 < b := ha.trans_le hab
  have hC := gammaRieszConstant_pos k r
  let B : ℝ := 4 * gammaRieszConstant k r * (a ^ gammaRieszLine r + b ^ gammaRieszLine r) / Real.pi
  have hzero : Tendsto (fun T : ℝ => B * T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (gammaRieszTailHeight k b), hzero.eventually (gt_mem_nhds hε)] with T hT hsmall
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hTx := (gammaRieszTailHeight_mono hx0 hx.2 k).trans hT
  have hT0 : 0 < T := by linarith [(gammaRieszTailHeight_properties hT).1]
  have hpow : x ^ gammaRieszLine r ≤ a ^ gammaRieszLine r + b ^ gammaRieszLine r := by
    by_cases hr : 0 ≤ gammaRieszLine r
    · exact (Real.rpow_le_rpow hx0.le hx.2 hr).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
    · exact (Real.rpow_le_rpow_of_nonpos ha hx.1 (le_of_not_ge hr)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hb.le _))
  rw [dist_eq_norm]
  apply (norm_gammaRieszKernel_sub_cutoff_le hk hr0 hr2 hx0 hTx).trans_lt
  apply lt_of_le_of_lt _ hsmall
  calc
    _ ≤ 4 * gammaRieszConstant k r * (a ^ gammaRieszLine r + b ^ gammaRieszLine r) /
        (Real.pi * Real.sqrt T) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = B * T ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hT0.le, ← Real.sqrt_eq_rpow]
      unfold B
      ring

end
end Dubon2026

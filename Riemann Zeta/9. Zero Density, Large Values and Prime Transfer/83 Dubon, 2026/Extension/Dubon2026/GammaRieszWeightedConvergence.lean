import Dubon2026.GammaRieszFiniteDerivative

/-! # Compact uniform convergence of the actual weighted and dilated Riesz cutoffs -/

namespace Dubon2026

open Complex Set Filter
open scoped Topology

noncomputable section

/-- The genuine weighted cutoffs converge uniformly after every fixed positive dilation. -/
theorem tendstoUniformlyOn_gammaRieszWeightedCutoff {k r c a b : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun T x : ℝ => ((x ^ r : ℝ) : ℂ) * gammaRieszVerticalCutoff k r (c * x) (3 / 8) T)
      (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * gammaRieszKernel k r (c * x)) atTop (Icc a b) := by
  have hu := tendstoUniformlyOn_gammaRieszVerticalCutoff hk hr0 hr2 (mul_pos hc ha)
    (mul_le_mul_of_nonneg_left hab hc.le)
    (by unfold gammaRieszLine; linarith : gammaRieszLine r ≤ 3 / 8) (le_refl (3 / 8 : ℝ))
  have hb : 0 < b := ha.trans_le hab
  have hB : 0 < b ^ r + 1 := by positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) (ε / (b ^ r + 1)) (div_pos hε hB)] with T hT
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hsmall := hT (c * x) ⟨mul_le_mul_of_nonneg_left hx.1 hc.le, mul_le_mul_of_nonneg_left hx.2 hc.le⟩
  have hw : ‖((x ^ r : ℝ) : ℂ)‖ ≤ b ^ r + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le r)]
    exact (Real.rpow_le_rpow hx0.le hx.2 hr0).trans (by linarith)
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  rw [dist_eq_norm] at hsmall
  calc
    _ ≤ (b ^ r + 1) * ‖gammaRieszKernel k r (c * x) - gammaRieszVerticalCutoff k r (c * x) (3 / 8) T‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ < (b ^ r + 1) * (ε / (b ^ r + 1)) := mul_lt_mul_of_pos_left hsmall hB
    _ = ε := by field_simp

end
end Dubon2026

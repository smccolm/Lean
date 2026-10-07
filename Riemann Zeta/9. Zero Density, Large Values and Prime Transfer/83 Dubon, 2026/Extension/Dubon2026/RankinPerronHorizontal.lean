import Dubon2026.RankinPerronContinuation

/-! # Vanishing of both genuine Rankin Perron horizontal contour edges -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The actual general-level Perron horizontal integral has uniform inverse-square-root decay across the fixed strip. -/
theorem exists_rankinPerron_horizontal_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖HIntegral (rankinPerronContinuation f x) (-1 / 8) (9 / 8) t‖ ≤ C * |t| ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinPerronContinuation_strip_decay f hk hx
  refine ⟨(5 / 4) * C, by positivity, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp only [he, abs_zero] at ht; linarith
  have hc : ContinuousOn (fun β : ℝ => rankinPerronContinuation f x (gammaVerticalPoint β t))
      (uIcc (-1 / 8) (9 / 8)) := by
    intro β _
    apply ContinuousAt.continuousWithinAt
    apply (differentiableAt_rankinPerronContinuation f hx
      (by simpa only [gammaVerticalPoint_im] using ht0)).continuousAt.comp
    have hh : Continuous (fun β : ℝ => gammaVerticalPoint β t) := by unfold gammaVerticalPoint; fun_prop
    exact hh.continuousAt
  change ‖∫ β in (-1 / 8 : ℝ)..(9 / 8), rankinPerronContinuation f x (gammaVerticalPoint β t)‖ ≤ _
  calc
    _ ≤ ∫ β in (-1 / 8 : ℝ)..(9 / 8), ‖rankinPerronContinuation f x (gammaVerticalPoint β t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ in (-1 / 8 : ℝ)..(9 / 8), C * |t| ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_mono_on (by norm_num) hc.norm.intervalIntegrable
        (continuous_const.intervalIntegrable _ _) (fun β hβ => by
          simpa only [gammaVerticalPoint_im] using hCb (gammaVerticalPoint β t)
            (by simpa only [gammaVerticalPoint_re] using hβ.1)
            (by simpa only [gammaVerticalPoint_re] using hβ.2)
            (by simpa only [gammaVerticalPoint_im] using ht))
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Both genuine general-level Perron horizontal edges vanish; the statement retains their literal contour integrals. -/
theorem tendsto_rankinPerron_horizontal_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => HIntegral (rankinPerronContinuation f x) (-1 / 8) (9 / 8) T) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral (rankinPerronContinuation f x) (-1 / 8) (9 / 8) (-T)) atTop (𝓝 0) := by
  obtain ⟨C, _, hCb⟩ := exists_rankinPerron_horizontal_bound f hk hx
  have hz : Tendsto (fun T : ℝ => C * T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  constructor
  · apply squeeze_zero_norm' _ hz
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using
      hCb T (by rw [abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT)
  · apply squeeze_zero_norm' _ hz
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using
      hCb (-T) (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT)

end
end Dubon2026

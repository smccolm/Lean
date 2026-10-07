import Dubon2026.NewmanContourIdentity
import Dubon2026.NewmanContourBounds
import Dubon2026.NewmanHolomorphic

/-! # Analytic Tauberian convergence for the actual bounded-function Laplace transform -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The exact Cauchy identities and proved Laplace estimates bound the genuine truncation error. -/
theorem newman_tauberian_error_bound {f : ℝ → ℂ} {G : ℂ → ℂ} {B d R T : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hd : 0 < d) (hR : 0 < R) (hT : 0 ≤ T)
    (hG : DifferentiableOn ℂ G {z : ℂ | -d ≤ z.re})
    (heq : ∀ z : ℂ, 0 < z.re → G z = newmanLaplace f z) :
    ‖G 0 - newmanTruncatedLaplace f T 0‖ ≤ ‖1 / (2 * Real.pi * I)‖ *
      (24 * B / R + ‖newmanLeftContour (newmanContourIntegrand G T R) d R‖) := by
  let H := newmanTruncatedLaplace f T
  have hH : Differentiable ℂ H := differentiable_newmanTruncatedLaplace hfm hf hT
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0 le_rfl)
  have hg := newman_half_contour_formula hd hR hG T
  have hh := newman_half_contour_formula hR hR hH.differentiableOn T
  have hgi := newman_contour_border_integrable hd hR hG.continuousOn T
  have hhi := newman_contour_border_integrable hd hR hH.continuous.continuousOn T
  have hs : newmanRightContour (newmanContourIntegrand (G - H) T R) R =
      newmanRightContour (newmanContourIntegrand G T R) R -
        newmanRightContour (newmanContourIntegrand H T R) R := by
    rw [newmanContourIntegrand_sub, newmanRightContour_sub hd.le hR.le hgi hhi]
  have he : G 0 - H 0 = (1 / (2 * Real.pi * I)) *
      (newmanRightContour (newmanContourIntegrand (G - H) T R) R +
        newmanLeftContour (newmanContourIntegrand G T R) d R -
          newmanLeftContour (newmanContourIntegrand H T R) R R) := by
    rw [hs]
    linear_combination -hg + hh
  have hr := newman_right_square_bound hB hR (G := G - H) (T := T) (fun z hz => by
    simpa only [Pi.sub_apply, heq z hz, H] using norm_newmanLaplace_tail_le hfm hf hT hz)
  have hl := newman_left_square_bound hB hR (G := H) (T := T) (fun z hz =>
    norm_newmanTruncatedLaplace_left_le hf hz)
  change ‖G 0 - H 0‖ ≤ _
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  rw [show 24 * B / R = 12 * B / R + 12 * B / R by ring]
  linarith

/-- Analytic continuation of the genuine bounded Laplace transform across the whole boundary implies convergence of its actual truncations. -/
theorem newman_tauberian_truncated {f : ℝ → ℂ} {G : ℂ → ℂ} {B d : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hd : 0 < d) (hG : DifferentiableOn ℂ G {z : ℂ | -d ≤ z.re})
    (heq : ∀ z : ℂ, 0 < z.re → G z = newmanLaplace f z) :
    Tendsto (fun T : ℝ => newmanTruncatedLaplace f T 0) atTop (𝓝 (G 0)) := by
  let C : ℝ := ‖(1 : ℂ) / (2 * Real.pi * I)‖
  have hs : Tendsto (fun R : ℝ => C * (24 * B / R)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun R : ℝ => 24 * B / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using hdiv.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR, hr⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hs.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hl : Tendsto (fun T : ℝ => C * ‖newmanLeftContour (newmanContourIntegrand G T R) d R‖)
      atTop (𝓝 0) := by
    simpa using (newman_left_contour_tendsto_zero hd hR hG.continuousOn).norm.const_mul C
  filter_upwards [eventually_ge_atTop (0 : ℝ), hl.eventually (gt_mem_nhds (half_pos hε))] with T hT ht
  rw [dist_eq_norm, norm_sub_rev]
  have hb := newman_tauberian_error_bound hfm hf hd hR hT hG heq
  change ‖G 0 - newmanTruncatedLaplace f T 0‖ ≤ C * _ at hb
  apply hb.trans_lt
  nlinarith

/-- The actual improper integral converges to the continued Laplace transform at zero. -/
theorem newman_tauberian_integral {f : ℝ → ℂ} {G : ℂ → ℂ} {B d : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hd : 0 < d) (hG : DifferentiableOn ℂ G {z : ℂ | -d ≤ z.re})
    (heq : ∀ z : ℂ, 0 < z.re → G z = newmanLaplace f z) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (G 0)) := by
  apply (newman_tauberian_truncated hfm hf hd hG heq).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp [newmanTruncatedLaplace, intervalIntegral.integral_of_le hT]

end
end Dubon2026

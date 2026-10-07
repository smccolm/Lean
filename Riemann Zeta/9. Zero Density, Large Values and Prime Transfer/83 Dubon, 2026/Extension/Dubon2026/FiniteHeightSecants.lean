import Dubon2026.FiniteHeightDerivative
import Dubon2026.FiniteHeightContinuity
import Dubon2026.FiniteVerticalExceptions
import Dubon2026.FiniteExceptionalMeanValue

/-! # Secant bounds for the actual vertical logarithmic-derivative mean -/

namespace Dubon2026

open Complex Set

theorem finiteHeight_left_secant_le {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l σ T : ℝ} (hl : l < σ) (hT : 0 < T)
    (hσ : ∀ y ∈ Icc (-T) T, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0)
    (ht : ∀ s : ℂ, |s.im| = T → dirichletSum a N s ≠ 0) :
    (verticalLogMean a N σ T - verticalLogMean a N l T) / (σ - l) -
      Real.pi * (2 : ℝ) ^ N / T ≤ verticalLogDerivMean a N σ T := by
  obtain ⟨Z, hZ⟩ := exists_finite_vertical_segment_exceptions hN (ha.trans_ne one_ne_zero) l σ T
  have hh := image_sub_le_of_derivative_le_off_finset
    (fun x => verticalLogMean a N x T) (fun x => verticalLogDerivMean a N x T) Z l σ
    (verticalLogDerivMean a N σ T + Real.pi * (2 : ℝ) ^ N / T) hl.le
    (continuous_verticalLogMean hN (ha.trans_ne one_ne_zero) T hT.le).continuousOn (by
      intro x hx hxZ
      have hn := hZ x ⟨hx.1.le, hx.2.le⟩ hxZ
      exact ⟨hasDerivAt_verticalLogMean a N x T hT.le hn,
        verticalLogDerivMean_le_add hN ha hx.2.le hT
          (rectangle_boundary_ne_zero_of_segments hT.le hn hσ ht)⟩)
  have hdiv := (div_le_iff₀ (sub_pos.mpr hl)).mpr hh
  linarith

theorem finiteHeight_right_secant_ge {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {σ u T : ℝ} (hu : σ < u) (hT : 0 < T)
    (hσ : ∀ y ∈ Icc (-T) T, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0)
    (ht : ∀ s : ℂ, |s.im| = T → dirichletSum a N s ≠ 0) :
    verticalLogDerivMean a N σ T ≤
      (verticalLogMean a N u T - verticalLogMean a N σ T) / (u - σ) +
        Real.pi * (2 : ℝ) ^ N / T := by
  obtain ⟨Z, hZ⟩ := exists_finite_vertical_segment_exceptions hN (ha.trans_ne one_ne_zero) σ u T
  have hh := mul_sub_le_of_le_derivative_off_finset
    (fun x => verticalLogMean a N x T) (fun x => verticalLogDerivMean a N x T) Z σ u
    (verticalLogDerivMean a N σ T - Real.pi * (2 : ℝ) ^ N / T) hu.le
    (continuous_verticalLogMean hN (ha.trans_ne one_ne_zero) T hT.le).continuousOn (by
      intro x hx hxZ
      have hn := hZ x ⟨hx.1.le, hx.2.le⟩ hxZ
      refine ⟨hasDerivAt_verticalLogMean a N x T hT.le hn, ?_⟩
      have hbound := verticalLogDerivMean_le_add hN ha hx.1.le hT
        (rectangle_boundary_ne_zero_of_segments hT.le hσ hn ht)
      linarith)
  have hdiv := (le_div_iff₀ (sub_pos.mpr hu)).mpr hh
  linarith

end Dubon2026

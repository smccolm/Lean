import TaoTrudgianYang2025.ZetaDivisorVoronoi
import TaoTrudgianYang2025.ZetaSmoothDivisorTail

/-!
# The actual zeta local mean enters the native Voronoi expansion

The smoothing transition costs an arbitrarily small power tail on the
literal logarithmic band. These theorems assemble that estimate with
the physical zeta source and the native modulus-one Voronoi identity.
The transformed sums still need their Bessel and stationary analysis.
-/

noncomputable section

open Complex Filter MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_zetaSquareGaussianMean_smooth_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianMean T G - 2 * (zetaSmoothDivisorSum T G (Real.log T)).re| ≤
        C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareGaussianMean_short_approximation hδ
  obtain ⟨B₁, hB₁, htail⟩ := exists_zetaSmoothDivisor_log_tail_bound 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |zetaSquareGaussianMean T G - 2 * (zetaSmoothDivisorSum T G (Real.log T)).re| ≤
        (C + 2) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hG hwidth
    have hmain := hsource T G hTB hG hwidth
    have ht := htail T G hTB₁ hG (hscale.2.2 G hG hwidth).1
    simp only [neg_zero, Real.rpow_zero, mul_one] at ht
    have hre : |(zetaSmoothDivisorSum T G (Real.log T)).re -
        (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤ G :=
      (Complex.abs_re_le_norm
        (zetaSmoothDivisorSum T G (Real.log T) - zetaShortQuadraticDivisorSum T G (Real.log T))).trans ht
    have htri := abs_sub_le (zetaSquareGaussianMean T G)
      (2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re)
      (2 * (zetaSmoothDivisorSum T G (Real.log T)).re)
    have hdiff : |2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re -
        2 * (zetaSmoothDivisorSum T G (Real.log T)).re| ≤ 2 * G := by
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hre (by norm_num)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

theorem exists_zetaSquareLocalMean_le_smooth_divisor {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaSmoothDivisorSum T G (Real.log T)).re + C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_short_divisor hδ
  obtain ⟨B₁, hB₁, htail⟩ := exists_zetaSmoothDivisor_log_tail_bound 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaSmoothDivisorSum T G (Real.log T)).re +
          (C + 2 * Real.exp 1) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hG hwidth
    have hmain := hsource T G hTB hG hwidth
    have ht := htail T G hTB₁ hG (hscale.2.2 G hG hwidth).1
    simp only [neg_zero, Real.rpow_zero, mul_one] at ht
    have hre := (Complex.abs_re_le_norm
      (zetaSmoothDivisorSum T G (Real.log T) - zetaShortQuadraticDivisorSum T G (Real.log T))).trans ht
    simp only [Complex.sub_re] at hre
    have hreal : (zetaShortQuadraticDivisorSum T G (Real.log T)).re ≤
        (zetaSmoothDivisorSum T G (Real.log T)).re + G := by
      linarith [(abs_le.mp hre).1]
    have hscaled := mul_le_mul_of_nonneg_left hreal (by positivity : 0 ≤ 2 * Real.exp 1)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    have hextra := mul_le_mul_of_nonneg_left hGlog (by positivity : 0 ≤ 2 * Real.exp 1)
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2 * Real.exp 1, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

/-- Actual physical Gaussian mean, actual constructed source, actual
native transformed sums. All uniform thresholds precede the width. -/
theorem exists_zetaSquarePhysicalGaussian_voronoi_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaDivisorVoronoiMain T G (Real.log T) +
          zetaDivisorVoronoiMinus T G (Real.log T) +
          zetaDivisorVoronoiPlus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareGaussianMean_smooth_approximation hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hwidth
  have hT8 := hT₀.trans hT
  rw [← zetaSquareGaussianMean_eq_physical T hG,
    ← zetaSmoothDivisorSum_eq_voronoi (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hwidth

theorem exists_zetaSquareLocalMean_le_voronoi {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaDivisorVoronoiMain T G (Real.log T) +
          zetaDivisorVoronoiMinus T G (Real.log T) + zetaDivisorVoronoiPlus T G (Real.log T)).re +
            C * G * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_zetaSquareLocalMean_le_smooth_divisor hδ
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T G hT hG hwidth
  have hT8 := hT₀.trans hT
  rw [← zetaSmoothDivisorSum_eq_voronoi (by linarith : 0 < T) hG (Real.log_pos (by linarith))]
  exact hbound T G hT hG hwidth

end TaoTrudgianYang2025

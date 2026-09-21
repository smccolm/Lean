import TaoTrudgianYang2025.AtkinsonLeadingTruncation

/-!
# Actual physical zeta source with a finite leading-carrier sum

The polynomial truncation error is absorbed into the established physical
logarithmic error. The retained terms are actual oscillatory integrals,
not yet their sharp stationary main values.
-/

noncomputable section

open Complex Filter MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_atkinsonLeading_polynomial_log_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        C * G * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingSum_sub_polynomial_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        C * G * Real.log T := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ] with T hsupport hscale
    intro G hlower hupper N hN
    obtain ⟨hG, _, hwidth, _⟩ := hsupport.2 G hlower
    apply (hbound T G (Real.log T) (by linarith [hsupport.1]) hG
      (hscale.2.2 G hG hupper).1 hscale.2.1 hwidth N hN).trans
    exact le_mul_of_one_le_right (mul_nonneg hC.le hG.le) hscale.2.1
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨C, hC, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper N hN
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper N hN

theorem exists_zetaSquarePhysicalGaussian_atkinson_finite_approximation
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ :=
    exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_atkinsonLeading_polynomial_log_bound hδ
  refine ⟨C + 2 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper N hN
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper N hN
  have hr := (Complex.abs_re_le_norm
    (atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N)).trans he
  simp only [Complex.sub_re] at hr
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1, (abs_le.mp hm).2,
    (abs_le.mp hr).1, (abs_le.mp hr).2]

theorem exists_zetaSquareLocalMean_le_atkinson_finite {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_leading hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_atkinsonLeading_polynomial_log_bound hδ
  refine ⟨C + 2 * Real.exp 1 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper N hN
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper N hN
  have hr := (Complex.re_le_norm
    (atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N)).trans he
  simp only [Complex.sub_re] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * Real.exp 1)
  nlinarith

end TaoTrudgianYang2025

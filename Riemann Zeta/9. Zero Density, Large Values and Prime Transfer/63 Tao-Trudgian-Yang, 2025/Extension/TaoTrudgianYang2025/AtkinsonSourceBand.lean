import TaoTrudgianYang2025.AtkinsonSharpTruncation

/-!
# Physical zeta source with source-scale leading truncation

The actual Gaussian and local-mean theorems now require only a cutoff
N >= 36 T (log(T)/G)^2. The retained carriers have not been replaced by
a sum of stationary approximations with an assumed summed error.
-/

noncomputable section

open Complex Filter MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_atkinsonLeading_source_band_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingSum_sub_band_finite_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      ‖atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N‖ ≤
        (2 * C) * G := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ,
      eventually_const_log_pow_le_rpow 1 (by norm_num) 1 (η := 1 / 4) (by norm_num)] with
      T hsupport hscale hlog
    intro G hlower hupper N hN
    obtain ⟨hG0, hlog0, hwidth, _⟩ := hsupport.2 G hlower
    have hT : 1 ≤ T := by linarith [hsupport.1]
    have hG : 1 ≤ G := (Real.one_le_rpow hT hδ.le).trans hlower
    have hGT := (hscale.2.2 G hG0 hupper).1
    apply (hbound T G (Real.log T) hT hG hGT hscale.2.1 hwidth N hN).trans
    have h := mul_le_mul_of_nonneg_left
      (atkinsonBand_tail_scale_le hT hG0.le hGT hlog0.le
        (by simpa only [one_mul, pow_one] using hlog)) hC.le
    convert h using 1 <;> ring
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨2 * C, by positivity, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper N hN
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper N hN

private theorem one_le_log_of_sixteen_le {T : ℝ} (hT : 16 ≤ T) : 1 ≤ Real.log T := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < T)).2
  have h := exp_sub_one_le_two_mul (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  linarith

theorem exists_zetaSquarePhysicalGaussian_atkinson_band_approximation
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ :=
    exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_atkinsonLeading_source_band_bound hδ
  refine ⟨C + 2 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper N hN
  have hT16 : 16 ≤ T := hB.trans ((le_max_left _ _).trans hT)
  have hG : 0 < G := (Real.rpow_pos_of_pos (by linarith : 0 < T) δ).trans_le hlower
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper N hN
  have he' := he.trans (le_mul_of_one_le_right (mul_nonneg hD.le hG.le)
    (one_le_log_of_sixteen_le hT16))
  have hr := (Complex.abs_re_le_norm
    (atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N)).trans he'
  simp only [Complex.sub_re] at hr
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1, (abs_le.mp hm).2,
    (abs_le.mp hr).1, (abs_le.mp hr).2]

theorem exists_zetaSquareLocalMean_le_atkinson_band {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re +
          C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_leading hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_atkinsonLeading_source_band_bound hδ
  refine ⟨C + 2 * Real.exp 1 * D, by positivity, max B B₁, hB.trans (le_max_left _ _), ?_⟩
  intro T G hT hlower hupper N hN
  have hT16 : 16 ≤ T := hB.trans ((le_max_left _ _).trans hT)
  have hG : 0 < G := (Real.rpow_pos_of_pos (by linarith : 0 < T) δ).trans_le hlower
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper N hN
  have he' := he.trans (le_mul_of_one_le_right (mul_nonneg hD.le hG.le)
    (one_le_log_of_sixteen_le hT16))
  have hr := (Complex.re_le_norm
    (atkinsonLeadingSum T G (Real.log T) - atkinsonLeadingFiniteSum T G (Real.log T) N)).trans he'
  simp only [Complex.sub_re] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * Real.exp 1)
  nlinarith

end TaoTrudgianYang2025

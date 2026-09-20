import TaoTrudgianYang2025.ZetaAtkinsonK0

/-!
# Phase-corrected physical source with the modified-Bessel branch removed

The genuine physical zeta source is now the full logarithmic main term
plus the oscillatory Neumann-kernel divisor sum, both using the
source's saddle-regulating integer-lattice phase. The discarded K0
branch is bounded by the proved complete-series power saving, not by
a separately supplied error hypothesis.
-/

noncomputable section

open Complex Filter MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_zetaSquarePhysicalGaussian_atkinson_reduced {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re| ≤ C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquarePhysicalGaussian_atkinson_approximation hδ
  obtain ⟨B₁, hB₁, hplus⟩ := exists_zetaAtkinsonBesselPlus_powerSaving hδ 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re| ≤ (C + 2) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hlower hupper
    have hT0 : 0 < T := by linarith [hscale.1]
    have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
    have hm := hsource T G hTB hG hupper
    have hk := hplus T G hTB₁ hlower hupper
    simp only [neg_zero, Real.rpow_zero, mul_one] at hk
    have hkr := (Complex.abs_re_le_norm (zetaAtkinsonBesselPlus T G (Real.log T))).trans hk
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    simp only [Complex.add_re] at hm ⊢
    apply abs_le.mpr
    constructor <;> nlinarith [(abs_le.mp hm).1, (abs_le.mp hm).2,
      (abs_le.mp hkr).1, (abs_le.mp hkr).2]
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2, by positivity, max 16 T₁, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hT₁ T ((le_max_right _ _).trans hT) G hlower hupper

theorem exists_zetaSquareLocalMean_le_atkinson_reduced {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re + C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_bessel hδ
  obtain ⟨B₁, hB₁, hplus⟩ := exists_zetaAtkinsonBesselPlus_powerSaving hδ 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re +
            (C + 2 * Real.exp 1) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hlower hupper
    have hT0 : 0 < T := by linarith [hscale.1]
    have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
    have hm := hsource T G hTB hG hupper
    have hk := hplus T G hTB₁ hlower hupper
    simp only [neg_zero, Real.rpow_zero, mul_one] at hk
    have hkr := (Complex.re_le_norm (zetaAtkinsonBesselPlus T G (Real.log T))).trans hk
    have hscaled := mul_le_mul_of_nonneg_left hkr (by positivity : 0 ≤ 2 * Real.exp 1)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    have herror := mul_le_mul_of_nonneg_left hGlog (by positivity : 0 ≤ 2 * Real.exp 1)
    simp only [Complex.add_re] at hm ⊢
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2 * Real.exp 1, by positivity, max 16 T₁, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hT₁ T ((le_max_right _ _).trans hT) G hlower hupper

end TaoTrudgianYang2025

import TaoTrudgianYang2025.ZetaAtkinsonMainWeight

/-!
# Uniform bound for the actual logarithmic Voronoi main integral

Positive compact support is derived from the source cutoff. The
native logarithmic reflection estimate consumes the complete proved
amplitude variation, cancelling its square-root height factor.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaAtkinsonMainIntegrand (T G L x : ℝ) : ℂ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ) * zetaAtkinsonDivisorTest T G L x

theorem integrable_zetaAtkinsonMainIntegrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Integrable (zetaAtkinsonMainIntegrand T G L) := by
  have hT0 : 0 < T := by linarith
  let hg := zetaAtkinsonDivisorVoronoiTest hT0 hG hL
  have hi : Integrable (zetaAtkinsonDivisorTest T G L) :=
    hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  have hm : AEStronglyMeasurable (zetaAtkinsonMainIntegrand T G L) :=
    ((Complex.measurable_ofReal.comp (Real.measurable_log.add_const
      (2 * Real.eulerMascheroniConstant))).aestronglyMeasurable).mul hg.continuous.aestronglyMeasurable
  apply (hi.norm.const_mul (Real.log T + 2 * Real.eulerMascheroniConstant)).mono' hm
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : zetaAtkinsonDivisorTest T G L x = 0
  · simp only [zetaAtkinsonMainIntegrand, hx, mul_zero, norm_zero, le_refl]
  have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
    rw [← support_zetaAtkinsonDivisorTest]
    exact hx
  have hp := support_zetaSmoothDivisorTest_physical hT0 hG hL hwidth hs
  rw [zetaAtkinsonMainIntegrand, norm_mul]
  exact mul_le_mul_of_nonneg_right ((intervalC1Bound_source_log hT).norm_le x hp) (norm_nonneg _)

theorem zetaAtkinsonVoronoiMain_eq_reflection {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    zetaAtkinsonVoronoiMain T G L =
      ∫ x in (T / 16)..T, zetaAtkinsonMainWeight T G L x * ((x : ℂ)⁻¹ *
        Complex.exp (((T * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I)) := by
  have he : zetaAtkinsonVoronoiMain T G L =
      ∫ x : ℝ in Icc (T / 16) T,
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * zetaAtkinsonDivisorTest T G L x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (fun x hx => (by positivity : 0 < T / 16).trans_le hx.1)
    intro x hx
    have hz : zetaAtkinsonDivisorTest T G L x = 0 := by
      by_contra hn
      have hs : x ∈ Function.support (zetaSmoothDivisorTest T G L) := by
        rw [← support_zetaAtkinsonDivisorTest]
        exact hn
      exact hx.2 (support_zetaSmoothDivisorTest_physical hT hG hL hwidth hs)
    rw [hz, mul_zero]
  rw [he, intervalIntegral.integral_of_le (by linarith : T / 16 ≤ T),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact (zetaAtkinsonMainWeight_carrier hT
    (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1) G L).symm

theorem exists_norm_zetaAtkinsonVoronoiMain_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L → 8 * L ≤ G →
      ‖zetaAtkinsonVoronoiMain T G L‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hweight⟩ := exists_intervalC1Bound_zetaAtkinsonMainWeight
  refine ⟨20 * C, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  rw [zetaAtkinsonVoronoiMain_eq_reflection hT0 hG hL hwidth]
  have h := (hweight T G L hT hlog hG hGT hL).reflection
    (by linarith : 1 ≤ T) (by positivity : 0 < T / 16) (by linarith : T / 16 ≤ T)
  convert h using 1
  have hs : Real.sqrt T ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hT0)
  field_simp

theorem exists_zetaAtkinsonVoronoiMain_log_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonVoronoiMain T G (Real.log T)‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonVoronoiMain_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonVoronoiMain T G (Real.log T)‖ ≤ C * G * Real.log T := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ] with T hsupport hscale
    intro G hlower hupper
    obtain ⟨hG, hlog, hwidth, _⟩ := hsupport.2 G hlower
    exact hbound T G (Real.log T) hsupport.1 hscale.2.1 hG
      (hscale.2.2 G hG hupper).1 hlog hwidth
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨C, hC, max 16 B, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper

end TaoTrudgianYang2025

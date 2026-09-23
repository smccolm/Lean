import TaoTrudgianYang2025.SargosQuarticNearCount

/-!
# A weighted fourth moment for the literal quadratic-plus-quartic sum

The source interval is (N,2N]; the gamma window is [-N^-3,N^-3].
The estimate has no assumed counting or analytic input. Prefix maxima
and slowly varying phase perturbations are subsequent obligations.
-/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosQuartic_window_le_source_count (N : ℕ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {δ lambda : ℝ} (hδ : 0 < δ) (hlambda : 0 < lambda)
    (ha : 1/δ ≤ N) (hb : 1/lambda ≤ (N : ℝ)^3) (c d : ℝ) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda), ‖sargosQuarticSum N z α γ‖^4) ≤
      (16*δ*lambda)*((sargosFourthNearSolutions N).card : ℝ) := by
  simp_rw [sargosQuarticSum_norm_four_eq_pair_norm_sq]
  have h := sargosPlanar_window_le_nearPairs
    ((sargosSourceInterval N) ×ˢ (sargosSourceInterval N))
    (sargosPairCoefficient z) sargosSquarePairFrequency sargosFourthPairFrequency
    (fun _ hp => sargosPairCoefficient_norm_le_one hz hp) hδ hlambda c d
  exact h.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast card_sargosQuarticNearPairs_le_source ha hb)
    (by positivity : 0 ≤ 16*δ*lambda))

theorem sargosQuartic_fourth_moment {N : ℕ} (hN : 1 ≤ N) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {Δ : ℝ} (hΔ : 1/(N : ℝ) ≤ Δ) :
    (∫ α in Icc (0 : ℝ) Δ,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3), ‖sargosQuarticSum N z α γ‖^4) ≤
        131072*Δ/(N : ℝ)*(1+Real.log N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hΔpos : 0 < Δ := (one_div_pos.mpr hNpos).trans_le hΔ
  have hδcut : 1/Δ ≤ (N : ℝ) := by
    apply (div_le_iff₀ hΔpos).mpr
    have hm := mul_le_mul_of_nonneg_right hΔ hNpos.le
    have hcancel : (1/(N : ℝ))*(N : ℝ) = 1 := by field_simp
    rw [hcancel] at hm
    nlinarith
  have hlambda : 0 < 2/(N : ℝ)^3 := by positivity
  have hlambdacut : 1/(2/(N : ℝ)^3) ≤ (N : ℝ)^3 := by
    have he : 1/(2/(N : ℝ)^3) = (N : ℝ)^3/2 := by field_simp
    rw [he]
    nlinarith [pow_pos hNpos 3]
  have hwindow := sargosQuartic_window_le_source_count N z hz hΔpos hlambda
    hδcut hlambdacut 0 (-(1/(N : ℝ)^3))
  have hend : -(1/(N : ℝ)^3)+2/(N : ℝ)^3 = 1/(N : ℝ)^3 := by ring
  rw [zero_add,hend] at hwindow
  calc
    _ ≤ (16*Δ*(2/(N : ℝ)^3))*((sargosFourthNearSolutions N).card : ℝ) := hwindow
    _ ≤ (16*Δ*(2/(N : ℝ)^3))*(4096*(N : ℝ)^2*(1+Real.log N)) :=
      mul_le_mul_of_nonneg_left (card_sargosFourthNearSolutions_le_log hN) (by positivity)
    _ = _ := by
      field_simp
      ring

end TaoTrudgianYang2025

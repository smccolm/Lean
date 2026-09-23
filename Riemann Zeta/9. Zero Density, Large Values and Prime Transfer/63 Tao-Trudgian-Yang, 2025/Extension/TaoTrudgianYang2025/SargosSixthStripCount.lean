import TaoTrudgianYang2025.SargosSixthBaseMoment

/-! The count on any physical height strip reduces to the same actual base moment. -/

noncomputable section

open MeasureTheory Set Filter

namespace TaoTrudgianYang2025

theorem sargosQuartic_power_rectangle_mono (N p : ℕ) (z : ℤ → ℂ)
    {a b c d a' b' c' d' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    (∫ α in Icc a b, ∫ γ in Icc c d, ‖sargosQuarticSum N z α γ‖^p) ≤
      ∫ α in Icc a' b', ∫ γ in Icc c' d', ‖sargosQuarticSum N z α γ‖^p := by
  calc
    _ ≤ ∫ α in Icc a b, ∫ γ in Icc c' d', ‖sargosQuarticSum N z α γ‖^p := by
      apply integral_mono (integrable_sargosQuarticNormPower_outer N p z a b c d)
        (integrable_sargosQuarticNormPower_outer N p z a b c' d')
      intro α
      exact setIntegral_mono_set (integrable_sargosQuarticNormPower_inner N p z α c' d')
        (Eventually.of_forall (fun γ => pow_nonneg (norm_nonneg _) p))
        (Icc_subset_Icc hc hd).eventuallyLE
    _ ≤ _ := setIntegral_mono_set
      (integrable_sargosQuarticNormPower_outer N p z a' b' c' d')
      (Eventually.of_forall (fun α => integral_nonneg (fun γ => pow_nonneg (norm_nonneg _) p)))
      (Icc_subset_Icc ha hb).eventuallyLE

theorem sargosQuartic_central_strip_le_base (N : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hA1 : A ≤ 1) (hB : B ≤ 1/(N : ℝ)^3) :
    (∫ α in Icc (-A) A, ∫ γ in Icc (-B) B,
      ‖sargosQuarticSum N (fun _ => 1) α γ‖^6) ≤ 2*sargosSixthBaseMoment N :=
  (sargosQuartic_power_rectangle_mono N 6 (fun _ => 1) le_rfl le_rfl
    (neg_le_neg hB) hB).trans (sargosQuartic_central_sixth_le_base N hA hA1)

theorem sargos_strip_width_ratio {N : ℕ} (hN : 1 ≤ N)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    lambda/min lambda (2/(N : ℝ)^3) ≤ 1+lambda*(N : ℝ)^3 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  by_cases hl : lambda ≤ 2/(N : ℝ)^3
  · rw [min_eq_left hl,div_self hlambda.ne']
    have hn : 0 ≤ lambda*(N : ℝ)^3 := by positivity
    linarith
  · rw [min_eq_right (le_of_not_ge hl)]
    have he : lambda/(2/(N : ℝ)^3) = lambda*(N : ℝ)^3/2 := by field_simp
    rw [he]
    have hn : 0 ≤ lambda*(N : ℝ)^3 := by positivity
    linarith

theorem sargosMomentNearCount_unit_strip_le_base {N : ℕ} (hN : 1 ≤ N)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    lambda*(sargosMomentNearCount N 3 (1/((1 : ℝ)*(N : ℝ)^2))
      (1/(lambda*(N : ℝ)^4)) : ℝ) ≤
      128*(1+lambda*(N : ℝ)^3)*sargosSixthBaseMoment N := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let μ : ℝ := min lambda (2/(N : ℝ)^3)
  have hμ : 0 < μ := lt_min hlambda (by positivity)
  have hμLambda : μ ≤ lambda := min_le_left _ _
  have hμN : μ/2 ≤ 1/(N : ℝ)^3 := by
    dsimp [μ]
    calc
      _ ≤ (2/(N : ℝ)^3)/2 :=
        div_le_div_of_nonneg_right (min_le_right lambda (2/(N : ℝ)^3)) (by norm_num)
      _ = _ := by ring
  have hc := sargosMomentNearCount_window_le_central hN 3
    (by norm_num : (0 : ℝ) < 1) hμ (le_refl (1 : ℝ)) hμLambda
  have hj := sargosQuartic_central_strip_le_base N
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hμN
  have hr := sargos_strip_width_ratio hN hlambda
  calc
    _ ≤ lambda*((64/((1 : ℝ)*μ))*(∫ α in Icc (-((1 : ℝ)/2)) ((1 : ℝ)/2),
        ∫ γ in Icc (-(μ/2)) (μ/2), ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*3))) :=
      mul_le_mul_of_nonneg_left hc hlambda.le
    _ ≤ lambda*((64/((1 : ℝ)*μ))*(2*sargosSixthBaseMoment N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj (by positivity)) hlambda.le
    _ = 128*(lambda/μ)*sargosSixthBaseMoment N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by norm_num)) (sargosSixthBaseMoment_nonneg N)

end TaoTrudgianYang2025

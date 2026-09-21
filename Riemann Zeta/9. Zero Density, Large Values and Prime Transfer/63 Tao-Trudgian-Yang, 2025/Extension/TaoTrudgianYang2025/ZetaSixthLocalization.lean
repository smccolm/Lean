import TaoTrudgianYang2025.ZetaPerronEntry

/-!
# Sixth-order localization below height exponent three halves

The stronger cutoff decay is applied to the actual shifted Mellin integral.
The resulting far tail is bounded by a fixed constant times N^(11/2)/T^4.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.cutoff_critical_integrand_sixth_far_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t u : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) (hu : u ∉ zetaMellinSourceWindow P.T t) :
    ‖zetaCutoffCriticalIntegrand a b t u‖ ≤
      (30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ)) * |u| ^ (-5 : ℝ) := by
  obtain ⟨habs, htime⟩ := zetaMellin_far_abs P.T_pos ht hu
  have huPos : 0 < |u| := (by linarith [P.T_pos] : 0 < P.T / 2).trans habs
  have hweight : 1 + |u + t| ≤ 5 * (1 + |u|) := by
    have := abs_add_le u t
    linarith
  have hz := (norm_zeta_mellin_boundary (c := 1 / 2) (Or.inl rfl) (u + t)).trans
    (mul_le_mul_of_nonneg_left hweight (by norm_num))
  have hm := P.cutoff_mellin_bound hactive hne (σ := 1 / 2) le_rfl (j := 6) (by norm_num) u
  norm_num only [show (1 / 2 : ℝ) + (6 : ℕ) - 1 = 11 / 2 by norm_num] at hm
  have hden : 0 < 1 + |u| := by positivity
  have hfactor : 0 ≤ 30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (zetaCutoffMellinConstant_pos _ _).le)
      (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)
  rw [zetaCutoffCriticalIntegrand_eq, norm_mul]
  calc
    _ ≤ (6 * (5 * (1 + |u|))) *
        (zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / (1 + |u|) ^ 6) :=
      mul_le_mul hz hm (norm_nonneg _) (by positivity)
    _ = (30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ)) / (1 + |u|) ^ 5 := by
      field_simp
      ring
    _ ≤ (30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ)) / |u| ^ 5 := by
      apply div_le_div_of_nonneg_left hfactor (pow_pos huPos 5)
      exact pow_le_pow_left₀ huPos.le (by linarith) 5
    _ = _ := by rw [div_eq_mul_inv, Real.rpow_neg huPos.le, Real.rpow_ofNat]

theorem ZetaLargeValuePattern.cutoff_critical_sixth_far_integral (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 := by
  let C : ℝ := 30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := (zetaCutoffMellinConstant_pos 6 (1 / 2)).le
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  have hhalf : 0 < P.T / 2 := by linarith [P.T_pos]
  have htail : IntegrableOn (fun u : ℝ => C * |u| ^ (-5 : ℝ)) (Icc (-(P.T / 2)) (P.T / 2))ᶜ :=
    (integrableOn_abs_rpow_compl_Icc (by norm_num) hhalf).const_mul C
  have hsubset := zetaMellinSourceWindow_compl_subset ht
  calc
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, ‖zetaCutoffCriticalIntegrand a b t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, C * |u| ^ (-5 : ℝ) := by
      apply integral_mono_ae (P.integrable_cutoff_critical_integrand hactive t).norm.integrableOn
        (htail.mono_set hsubset)
      filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with u hu
      exact P.cutoff_critical_integrand_sixth_far_bound hactive hne ht hu
    _ ≤ ∫ u : ℝ in (Icc (-(P.T / 2)) (P.T / 2))ᶜ, C * |u| ^ (-5 : ℝ) :=
      setIntegral_mono_set htail (Eventually.of_forall fun u =>
        mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _))
          (Eventually.of_forall hsubset)
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc (by norm_num) hhalf]
      norm_num only [show (-5 : ℝ) + 1 = -4 by norm_num]
      rw [Real.rpow_neg hhalf.le, Real.rpow_ofNat]
      dsimp [C]
      field_simp [P.T_pos.ne']
      ring


end TaoTrudgianYang2025

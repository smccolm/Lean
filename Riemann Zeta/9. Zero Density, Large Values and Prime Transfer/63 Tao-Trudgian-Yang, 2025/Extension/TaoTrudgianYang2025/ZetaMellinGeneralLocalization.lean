import TaoTrudgianYang2025.ZetaMellinGeneralShift
import TaoTrudgianYang2025.ZetaMellinLocalization
import TaoTrudgianYang2025.ZetaRealMomentTransfer

/-!
# Localization on an arbitrary fixed line below the zeta pole

The fourth-order cutoff gives an explicit far integral bound proportional
to N^(c+3)/T^2. The constant retains its dependence on 1-c.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

def zetaCutoffLineIntegrand (a b : ℕ) (c t u : ℝ) : ℂ :=
  zetaMellinIntegrand (fun x => (zetaIntervalCutoff a b x : ℂ)) t
    ((c : ℂ) + (u : ℂ) * I)

theorem zetaCutoffLineIntegrand_eq (a b : ℕ) (c t u : ℝ) :
    zetaCutoffLineIntegrand a b c t u =
      riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
        mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((c : ℂ) + (u : ℂ) * I) := by
  unfold zetaCutoffLineIntegrand zetaMellinIntegrand
  congr 2
  push_cast
  ring

theorem ZetaLargeValuePattern.integrable_cutoff_line_integrand (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    Integrable (zetaCutoffLineIntegrand a b c t) :=
  integrable_zetaMellin_left_boundary (zetaIntervalCutoffTest a b (P.active_left_pos hactive))
    hc hc1 t


theorem ZetaLargeValuePattern.cutoff_line_integrand_far_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1)
    {t u : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) (hu : u ∉ zetaMellinSourceWindow P.T t) :
    ‖zetaCutoffLineIntegrand a b c t u‖ ≤
      ((5*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ)) * |u| ^ (-3 : ℝ) := by
  obtain ⟨habs, htime⟩ := zetaMellin_far_abs P.T_pos ht hu
  have huPos : 0 < |u| := (by linarith [P.T_pos] : 0 < P.T / 2).trans habs
  have hweight : 1 + |u + t| ≤ 5 * (1 + |u|) := by
    have := abs_add_le u t
    linarith
  have hz := (norm_zeta_mellin_left_boundary hc hc1 (u + t)).trans
    (mul_le_mul_of_nonneg_left hweight (by positivity))
  have hm := P.cutoff_mellin_bound hactive hne (σ := c) hc (j := 4) (by norm_num) u
  norm_num only [Nat.cast_ofNat] at hm
  rw [show c + (4 : ℝ) - 1 = c+3 by ring] at hm
  have hden : 0 < 1 + |u| := by positivity
  have hfactor : 0 ≤ (5*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (zetaCutoffMellinConstant_pos _ _).le)
      (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)
  rw [zetaCutoffLineIntegrand_eq, norm_mul]
  calc
    _ ≤ ((1/(1-c)+2) * (5 * (1 + |u|))) *
        (zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) / (1 + |u|) ^ 4) :=
      mul_le_mul hz hm (norm_nonneg _) (by positivity)
    _ = ((5*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ)) / (1 + |u|) ^ 3 := by
      field_simp
    _ ≤ ((5*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ)) / |u| ^ 3 := by
      apply div_le_div_of_nonneg_left hfactor (pow_pos huPos 3)
      exact pow_le_pow_left₀ huPos.le (by linarith) 3
    _ = _ := by rw [div_eq_mul_inv, Real.rpow_neg huPos.le, Real.rpow_ofNat]

theorem ZetaLargeValuePattern.cutoff_line_far_integral (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, zetaCutoffLineIntegrand a b c t u‖ ≤
      (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) / P.T ^ 2 := by
  let C : ℝ := (5*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := (zetaCutoffMellinConstant_pos 4 c).le
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  have hhalf : 0 < P.T / 2 := by linarith [P.T_pos]
  have htail : IntegrableOn (fun u : ℝ => C * |u| ^ (-3 : ℝ)) (Icc (-(P.T / 2)) (P.T / 2))ᶜ :=
    (integrableOn_abs_rpow_compl_Icc (by norm_num) hhalf).const_mul C
  have hsubset := zetaMellinSourceWindow_compl_subset ht
  calc
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, ‖zetaCutoffLineIntegrand a b c t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, C * |u| ^ (-3 : ℝ) := by
      apply integral_mono_ae (P.integrable_cutoff_line_integrand hactive hc hc1 t).norm.integrableOn
        (htail.mono_set hsubset)
      filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with u hu
      exact P.cutoff_line_integrand_far_bound hactive hne hc hc1 ht hu
    _ ≤ ∫ u : ℝ in (Icc (-(P.T / 2)) (P.T / 2))ᶜ, C * |u| ^ (-3 : ℝ) :=
      setIntegral_mono_set htail (Eventually.of_forall fun u =>
        mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _))
          (Eventually.of_forall hsubset)
    _ = _ := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc (by norm_num) hhalf]
      norm_num only [show (-3 : ℝ) + 1 = -2 by norm_num]
      rw [Real.rpow_neg hhalf.le, Real.rpow_ofNat]
      dsimp [C]
      field_simp [P.T_pos.ne']
      ring


end TaoTrudgianYang2025

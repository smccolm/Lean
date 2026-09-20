import TaoTrudgianYang2025.ZetaMellinUniform
import TaoTrudgianYang2025.ZetaMellinShift
import TaoTrudgianYang2025.ZetaMomentTransfer
import GuthMaynard.TypeIIFourthMomentReduction

/-!
# Localization of the exact coefficient-one Mellin integral

The near integral is the source convolution window. The far integral is
bounded uniformly in the actual scale using fourth-order cutoff decay.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaMellinSourceWindow (T t : ℝ) : Set ℝ := Icc (T / 2 - t) (3 * T - t)

def zetaCutoffCriticalIntegrand (a b : ℕ) (t u : ℝ) : ℂ :=
  zetaMellinIntegrand (fun x => (zetaIntervalCutoff a b x : ℂ)) t
    (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)

theorem zetaCutoffCriticalIntegrand_eq (a b : ℕ) (t u : ℝ) :
    zetaCutoffCriticalIntegrand a b t u =
      riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * I) *
        mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
  unfold zetaCutoffCriticalIntegrand zetaMellinIntegrand
  congr 2
  push_cast
  ring

theorem ZetaLargeValuePattern.integrable_cutoff_critical_integrand (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (t : ℝ) :
    Integrable (zetaCutoffCriticalIntegrand a b t) :=
  integrable_zetaMellin_boundary (zetaIntervalCutoffTest a b (P.active_left_pos hactive))
    (Or.inl rfl) t

theorem zetaMellinSourceWindow_compl_subset {T t : ℝ} (ht : t ∈ Icc T (2 * T)) :
    (zetaMellinSourceWindow T t)ᶜ ⊆ (Icc (-(T / 2)) (T / 2))ᶜ := by
  intro u hu hsmall
  apply hu
  change T / 2 - t ≤ u ∧ u ≤ 3 * T - t
  constructor <;> linarith [hsmall.1, hsmall.2, ht.1, ht.2]

theorem zetaMellin_far_abs {T t u : ℝ} (hT : 0 < T) (ht : t ∈ Icc T (2 * T))
    (hu : u ∉ zetaMellinSourceWindow T t) : T / 2 < |u| ∧ |t| ≤ 4 * |u| := by
  have hnot := zetaMellinSourceWindow_compl_subset ht hu
  have habs : T / 2 < |u| := lt_of_not_ge (fun h => hnot (abs_le.mp h))
  refine ⟨habs, ?_⟩
  rw [abs_of_nonneg (hT.le.trans ht.1)]
  linarith [ht.2]

theorem ZetaLargeValuePattern.cutoff_critical_integrand_far_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t u : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) (hu : u ∉ zetaMellinSourceWindow P.T t) :
    ‖zetaCutoffCriticalIntegrand a b t u‖ ≤
      (30 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ)) * |u| ^ (-3 : ℝ) := by
  obtain ⟨habs, htime⟩ := zetaMellin_far_abs P.T_pos ht hu
  have huPos : 0 < |u| := (by linarith [P.T_pos] : 0 < P.T / 2).trans habs
  have hweight : 1 + |u + t| ≤ 5 * (1 + |u|) := by
    have := abs_add_le u t
    linarith
  have hz := (norm_zeta_mellin_boundary (c := 1 / 2) (Or.inl rfl) (u + t)).trans
    (mul_le_mul_of_nonneg_left hweight (by norm_num))
  have hm := P.cutoff_mellin_bound hactive hne (σ := 1 / 2) le_rfl (j := 4) (by norm_num) u
  norm_num only [show (1 / 2 : ℝ) + (4 : ℕ) - 1 = 7 / 2 by norm_num] at hm
  have hden : 0 < 1 + |u| := by positivity
  have hfactor : 0 ≤ 30 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (zetaCutoffMellinConstant_pos _ _).le)
      (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)
  rw [zetaCutoffCriticalIntegrand_eq, norm_mul]
  calc
    _ ≤ (6 * (5 * (1 + |u|))) *
        (zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / (1 + |u|) ^ 4) :=
      mul_le_mul hz hm (norm_nonneg _) (by positivity)
    _ = (30 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ)) / (1 + |u|) ^ 3 := by
      field_simp
      ring
    _ ≤ (30 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ)) / |u| ^ 3 := by
      apply div_le_div_of_nonneg_left hfactor (pow_pos huPos 3)
      exact pow_le_pow_left₀ huPos.le (by linarith) 3
    _ = _ := by rw [div_eq_mul_inv, Real.rpow_neg huPos.le, Real.rpow_ofNat]

theorem ZetaLargeValuePattern.cutoff_critical_far_integral (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 := by
  let C : ℝ := 30 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := (zetaCutoffMellinConstant_pos 4 (1 / 2)).le
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  have hhalf : 0 < P.T / 2 := by linarith [P.T_pos]
  have htail : IntegrableOn (fun u : ℝ => C * |u| ^ (-3 : ℝ)) (Icc (-(P.T / 2)) (P.T / 2))ᶜ :=
    (integrableOn_abs_rpow_compl_Icc (by norm_num) hhalf).const_mul C
  have hsubset := zetaMellinSourceWindow_compl_subset ht
  calc
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, ‖zetaCutoffCriticalIntegrand a b t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, C * |u| ^ (-3 : ℝ) := by
      apply integral_mono_ae (P.integrable_cutoff_critical_integrand hactive t).norm.integrableOn
        (htail.mono_set hsubset)
      filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with u hu
      exact P.cutoff_critical_integrand_far_bound hactive hne ht hu
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

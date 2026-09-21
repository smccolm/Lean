import TaoTrudgianYang2025.ZetaSixthLocalization

/-!
# Actual short-height Perron entry using sixth-order localization

One uniform threshold derives the physical hypotheses for sigma >= 7/10
and tau >= 7/5, retaining both the residue and far tail before absorption.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.polynomial_norm_le_sixth_convolution_and_errors (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t +
        zetaCutoffMellinConstant 6 1 * P.N ^ 6 / (1 + |t|) ^ 6 +
        240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 := by
  have hidentity := P.polynomial_eq_critical_zeta_mellin hactive t
  simp_rw [← zetaCutoffCriticalIntegrand_eq] at hidentity
  rw [hidentity]
  have hsplit := integral_add_compl (s := zetaMellinSourceWindow P.T t)
    measurableSet_Icc (P.integrable_cutoff_critical_integrand hactive t)
  have hwhole : ‖∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t +
        240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (P.cutoff_critical_near_integral hactive hne t)
      (P.cutoff_critical_sixth_far_integral hactive hne ht))
  have hscalar : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I)‖ +
        ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u‖ := by
      simpa only [norm_mul] using norm_add_le
        (mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I))
        ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u)
    _ ≤ _ := by
      have hres := P.cutoff_mellin_residue_bound hactive hne (j := 6) (by norm_num) t
      have hscale := mul_le_mul_of_nonneg_right hscalar
        (norm_nonneg (∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u))
      nlinarith

def zetaSixthPerronError : ℝ :=
  zetaCutoffMellinConstant 6 1 + 240 * zetaCutoffMellinConstant 6 (1 / 2)

theorem zetaSixthPerronError_pos : 0 < zetaSixthPerronError := by
  unfold zetaSixthPerronError
  exact add_pos (zetaCutoffMellinConstant_pos _ _)
    (mul_pos (by norm_num) (zetaCutoffMellinConstant_pos _ _))

theorem ZetaLargeValuePattern.sixth_perron_entry (P : ZetaLargeValuePattern)
    (hscale : P.N ^ (11 / 8 : ℝ) ≤ P.T) (hvalue : 2 * zetaSixthPerronError ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  have hne := P.active_nonempty_of_mem_ordinates ht
  have hinterval : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hscale
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by norm_num : (1 : ℝ) ≤ 11 / 8)
  have hresPower : P.N ^ 6 ≤ (1 + |t|) ^ 6 :=
    pow_le_pow_left₀ hNpos.le (by linarith [hinterval.1, le_abs_self t]) 6
  have hheightPower : P.N ^ (11 / 2 : ℝ) ≤ P.T ^ 4 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le (11 / 8)) hscale 4
    have heq : (P.N ^ (11 / 8 : ℝ)) ^ 4 = P.N ^ (11 / 2 : ℝ) := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hNpos.le]
      norm_num
    rwa [heq] at h
  have hres : zetaCutoffMellinConstant 6 1 * P.N ^ 6 / (1 + |t|) ^ 6 ≤
      zetaCutoffMellinConstant 6 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (1 + |t|) ^ 6)).2
    exact mul_le_mul_of_nonneg_left hresPower (zetaCutoffMellinConstant_pos _ _).le
  have hfar : 240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 ≤
      240 * zetaCutoffMellinConstant 6 (1 / 2) := by
    apply (div_le_iff₀ (pow_pos P.T_pos 4)).2
    exact mul_le_mul_of_nonneg_left hheightPower
      (mul_nonneg (by norm_num) (zetaCutoffMellinConstant_pos _ _).le)
  have hpoly := (P.large t ht).trans
    (P.polynomial_norm_le_sixth_convolution_and_errors hactive hne hinterval)
  unfold zetaSixthPerronError at hvalue
  unfold zetaPerronConstant
  nlinarith

/-- One threshold works for all source sigma and tau parameters in the
critical-line moment range. The actual exponent windows derive both
physical hypotheses of the proved Perron entry. -/
theorem exists_zetaSixthPerron_uniform_threshold :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ τ δ : ℝ, 7 / 10 ≤ σ → 7 / 5 ≤ τ → δ ≤ 1 / 80 →
        P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  have hevent : ∀ᶠ N : ℝ in atTop, 2 * zetaSixthPerronError ≤ N ^ (1 / 80 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 80)).eventually
      (eventually_ge_atTop (2 * zetaSixthPerronError))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro P hN σ τ δ hσ hτ hδ hT hV t ht
  apply P.sixth_perron_entry _ _ ht
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (11 / 8 : ℝ) ≤ τ - δ)).trans hT
  · exact (hN₀ P.N ((le_max_right _ _).trans hN)).trans
      ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (1 / 80 : ℝ) ≤ σ - δ)).trans hV)

end TaoTrudgianYang2025

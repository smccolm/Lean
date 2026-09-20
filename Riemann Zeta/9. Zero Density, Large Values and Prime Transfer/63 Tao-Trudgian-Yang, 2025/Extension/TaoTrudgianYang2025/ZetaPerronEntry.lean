import TaoTrudgianYang2025.ZetaMellinLocalization

/-!
# The actual coefficient-one entry into the source convolution

Both the moving-pole residue and the far integral are retained and bounded
before they are absorbed at genuinely large thresholds.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem integral_zetaMellinSourceWindow_convolution {T : ℝ} (hT : 0 < T) (t : ℝ) :
    (∫ u : ℝ in zetaMellinSourceWindow T t,
      zetaMomentKernel t (u + t) * zetaMomentCriticalNorm (u + t)) = zetaMomentConvolution T t := by
  rw [zetaMellinSourceWindow, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show T / 2 - t ≤ 3 * T - t by linarith)]
  rw [intervalIntegral.integral_comp_add_right
    (fun v => zetaMomentKernel t v * zetaMomentCriticalNorm v) t]
  simp only [sub_add_cancel, zetaMomentConvolution]

theorem ZetaLargeValuePattern.cutoff_critical_near_integral (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) (t : ℝ) :
    ‖∫ u : ℝ in zetaMellinSourceWindow P.T t, zetaCutoffCriticalIntegrand a b t u‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  let C := zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N
  have hcont : Continuous (fun u : ℝ =>
      C * (zetaMomentKernel t (u + t) * zetaMomentCriticalNorm (u + t))) :=
    continuous_const.mul (((continuous_zetaMomentKernel t).comp (by fun_prop)).mul
      (continuous_zetaMomentCriticalNorm.comp (by fun_prop)))
  have hdom : IntegrableOn (fun u : ℝ =>
      C * (zetaMomentKernel t (u + t) * zetaMomentCriticalNorm (u + t)))
        (zetaMellinSourceWindow P.T t) := hcont.continuousOn.integrableOn_Icc
  calc
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow P.T t, ‖zetaCutoffCriticalIntegrand a b t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow P.T t,
        C * (zetaMomentKernel t (u + t) * zetaMomentCriticalNorm (u + t)) := by
      apply integral_mono_ae (P.integrable_cutoff_critical_integrand hactive t).norm.integrableOn hdom
      filter_upwards with u
      rw [zetaCutoffCriticalIntegrand_eq, norm_mul]
      have h := mul_le_mul_of_nonneg_left
        (P.cutoff_critical_mellin_kernel hactive hne u)
          (norm_nonneg (riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * I)))
      convert h using 1
      dsimp [C, zetaMomentKernel, zetaMomentCriticalNorm]
      rw [add_sub_cancel_right]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_zetaMellinSourceWindow_convolution P.T_pos]

theorem ZetaLargeValuePattern.polynomial_norm_le_convolution_and_errors (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t +
        zetaCutoffMellinConstant 4 1 * P.N ^ 4 / (1 + |t|) ^ 4 +
        120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 := by
  have hidentity := P.polynomial_eq_critical_zeta_mellin hactive t
  simp_rw [← zetaCutoffCriticalIntegrand_eq] at hidentity
  rw [hidentity]
  have hsplit := integral_add_compl (s := zetaMellinSourceWindow P.T t)
    measurableSet_Icc (P.integrable_cutoff_critical_integrand hactive t)
  have hwhole : ‖∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t +
        120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (P.cutoff_critical_near_integral hactive hne t)
      (P.cutoff_critical_far_integral hactive hne ht))
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
      have hres := P.cutoff_mellin_residue_bound hactive hne (j := 4) (by norm_num) t
      have hscale := mul_le_mul_of_nonneg_right hscalar
        (norm_nonneg (∫ u : ℝ, zetaCutoffCriticalIntegrand a b t u))
      nlinarith

def zetaPerronError : ℝ :=
  zetaCutoffMellinConstant 4 1 + 120 * zetaCutoffMellinConstant 4 (1 / 2)

def zetaPerronConstant : ℝ := 2 * zetaCutoffMellinConstant 1 (1 / 2)

theorem zetaPerronError_pos : 0 < zetaPerronError := by
  unfold zetaPerronError
  exact add_pos (zetaCutoffMellinConstant_pos _ _)
    (mul_pos (by norm_num) (zetaCutoffMellinConstant_pos _ _))

theorem zetaPerronConstant_pos : 0 < zetaPerronConstant :=
  mul_pos (by norm_num) (zetaCutoffMellinConstant_pos _ _)

theorem ZetaLargeValuePattern.perron_entry (P : ZetaLargeValuePattern)
    (hscale : P.N ^ (7 / 4 : ℝ) ≤ P.T) (hvalue : 2 * zetaPerronError ≤ P.V)
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
      (by norm_num : (1 : ℝ) ≤ 7 / 4)
  have hresPower : P.N ^ 4 ≤ (1 + |t|) ^ 4 :=
    pow_le_pow_left₀ hNpos.le (by linarith [hinterval.1, le_abs_self t]) 4
  have hheightPower : P.N ^ (7 / 2 : ℝ) ≤ P.T ^ 2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le (7 / 4)) hscale 2
    have heq : (P.N ^ (7 / 4 : ℝ)) ^ 2 = P.N ^ (7 / 2 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hNpos.le]
      norm_num
    rwa [heq] at h
  have hres : zetaCutoffMellinConstant 4 1 * P.N ^ 4 / (1 + |t|) ^ 4 ≤
      zetaCutoffMellinConstant 4 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).2
    exact mul_le_mul_of_nonneg_left hresPower (zetaCutoffMellinConstant_pos _ _).le
  have hfar : 120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 ≤
      120 * zetaCutoffMellinConstant 4 (1 / 2) := by
    apply (div_le_iff₀ (pow_pos P.T_pos 2)).2
    exact mul_le_mul_of_nonneg_left hheightPower
      (mul_nonneg (by norm_num) (zetaCutoffMellinConstant_pos _ _).le)
  have hpoly := (P.large t ht).trans
    (P.polynomial_norm_le_convolution_and_errors hactive hne hinterval)
  unfold zetaPerronError at hvalue
  unfold zetaPerronConstant
  nlinarith

/-- One threshold works for all source sigma and tau parameters in the
critical-line moment range. The actual exponent windows derive both
physical hypotheses of the proved Perron entry. -/
theorem exists_zetaPerron_uniform_threshold :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ τ δ : ℝ, 1 / 2 ≤ σ → 2 ≤ τ → δ ≤ 1 / 4 →
        P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  have hevent : ∀ᶠ N : ℝ in atTop, 2 * zetaPerronError ≤ N ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (eventually_ge_atTop (2 * zetaPerronError))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro P hN σ τ δ hσ hτ hδ hT hV t ht
  apply P.perron_entry _ _ ht
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (7 / 4 : ℝ) ≤ τ - δ)).trans hT
  · exact (hN₀ P.N ((le_max_right _ _).trans hN)).trans
      ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (1 / 4 : ℝ) ≤ σ - δ)).trans hV)

theorem ZetaLargeValuePattern.twelfth_cardinality_of_perron (P : ZetaLargeValuePattern)
    (hscale : P.N ^ (7 / 4 : ℝ) ≤ P.T) (hvalue : 2 * zetaPerronError ≤ P.V) :
    (P.ordinates.card : ℝ) * P.V ^ 12 ≤
      zetaPerronConstant ^ 12 * P.N ^ 6 * zetaMomentLogLoss P.T ^ 12 * zetaTwelfthMoment P.T :=
  P.twelfth_cardinality_of_convolution zetaPerronConstant_pos
    (fun _ ht => P.perron_entry hscale hvalue ht)

end TaoTrudgianYang2025

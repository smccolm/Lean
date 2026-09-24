import TaoTrudgianYang2025.ZetaMellinGeneralLocalization

/-!
# Arbitrary-line Perron entry with the pole and far tail controlled

The scale condition is N^((c+3)/2) <= T. For every fixed 1/2 <= c < 1,
the source exponent range tau >= 2 eventually satisfies this condition.
The uniform exponent tolerance explicitly retains its dependence on 1-c.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.cutoff_line_mellin_kernel (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((c : ℂ)+(u : ℂ)*I)‖ ≤
      zetaCutoffMellinConstant 1 c*P.N^c/(1+|u|) := by
  have h := P.cutoff_mellin_bound hactive hne hc (j := 1) le_rfl u
  simpa only [Nat.cast_one,pow_one,add_sub_cancel_right] using h

theorem integral_zetaMellinSourceWindow_lineConvolution {T : ℝ} (hT : 0 < T) (c t : ℝ) :
    (∫ u : ℝ in zetaMellinSourceWindow T t,
      zetaMomentKernel t (u + t) * zetaMomentLineNorm c (u + t)) = zetaLineMomentConvolution c T t := by
  rw [zetaMellinSourceWindow, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show T / 2 - t ≤ 3 * T - t by linarith)]
  rw [intervalIntegral.integral_comp_add_right
    (fun v => zetaMomentKernel t v * zetaMomentLineNorm c v) t]
  simp only [sub_add_cancel, zetaLineMomentConvolution]

theorem ZetaLargeValuePattern.cutoff_line_near_integral (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    ‖∫ u : ℝ in zetaMellinSourceWindow P.T t, zetaCutoffLineIntegrand a b c t u‖ ≤
      zetaCutoffMellinConstant 1 c * P.N^c * zetaLineMomentConvolution c P.T t := by
  let C := zetaCutoffMellinConstant 1 c * P.N^c
  have hcont : Continuous (fun u : ℝ =>
      C * (zetaMomentKernel t (u + t) * zetaMomentLineNorm c (u + t))) :=
    continuous_const.mul (((continuous_zetaMomentKernel t).comp (by fun_prop)).mul
      ((continuous_zetaMomentLineNorm hc1.ne).comp (by fun_prop)))
  have hdom : IntegrableOn (fun u : ℝ =>
      C * (zetaMomentKernel t (u + t) * zetaMomentLineNorm c (u + t)))
        (zetaMellinSourceWindow P.T t) := hcont.continuousOn.integrableOn_Icc
  calc
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow P.T t, ‖zetaCutoffLineIntegrand a b c t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow P.T t,
        C * (zetaMomentKernel t (u + t) * zetaMomentLineNorm c (u + t)) := by
      apply integral_mono_ae (P.integrable_cutoff_line_integrand hactive hc hc1 t).norm.integrableOn hdom
      filter_upwards with u
      rw [zetaCutoffLineIntegrand_eq, norm_mul]
      have h := mul_le_mul_of_nonneg_left
        (P.cutoff_line_mellin_kernel hactive hne hc u)
          (norm_nonneg (riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I)))
      convert h using 1
      dsimp [C, zetaMomentKernel, zetaMomentLineNorm]
      rw [add_sub_cancel_right]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_zetaMellinSourceWindow_lineConvolution P.T_pos c]

theorem ZetaLargeValuePattern.polynomial_norm_le_lineConvolution_and_errors (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 c * P.N^c * zetaLineMomentConvolution c P.T t +
        zetaCutoffMellinConstant 4 1 * P.N ^ 4 / (1 + |t|) ^ 4 +
        (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) / P.T ^ 2 := by
  have hidentity := P.polynomial_eq_general_zeta_mellin hactive hc hc1 t
  simp_rw [← zetaCutoffLineIntegrand_eq] at hidentity
  rw [hidentity]
  have hsplit := integral_add_compl (s := zetaMellinSourceWindow P.T t)
    measurableSet_Icc (P.integrable_cutoff_line_integrand hactive hc hc1 t)
  have hwhole : ‖∫ u : ℝ, zetaCutoffLineIntegrand a b c t u‖ ≤
      zetaCutoffMellinConstant 1 c * P.N^c * zetaLineMomentConvolution c P.T t +
        (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) / P.T ^ 2 := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (P.cutoff_line_near_integral hactive hne hc hc1 t)
      (P.cutoff_line_far_integral hactive hne hc hc1 ht))
  have hscalar : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I)‖ +
        ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ u : ℝ, zetaCutoffLineIntegrand a b c t u‖ := by
      simpa only [norm_mul] using norm_add_le
        (mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I))
        ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaCutoffLineIntegrand a b c t u)
    _ ≤ _ := by
      have hres := P.cutoff_mellin_residue_bound hactive hne (j := 4) (by norm_num) t
      have hscale := mul_le_mul_of_nonneg_right hscalar
        (norm_nonneg (∫ u : ℝ, zetaCutoffLineIntegrand a b c t u))
      nlinarith

def zetaLinePerronError (c : ℝ) : ℝ :=
  zetaCutoffMellinConstant 4 1 + (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c

def zetaLinePerronConstant (c : ℝ) : ℝ := 2 * zetaCutoffMellinConstant 1 c

theorem zetaLinePerronError_pos {c : ℝ} (hc1 : c < 1) : 0 < zetaLinePerronError c := by
  unfold zetaLinePerronError
  exact add_pos (zetaCutoffMellinConstant_pos _ _)
    (mul_pos (by positivity) (zetaCutoffMellinConstant_pos _ _))

theorem zetaLinePerronConstant_pos (c : ℝ) : 0 < zetaLinePerronConstant c :=
  mul_pos (by norm_num) (zetaCutoffMellinConstant_pos _ _)

theorem ZetaLargeValuePattern.line_perron_entry (P : ZetaLargeValuePattern)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1)
    (hscale : P.N ^ ((c+3)/2 : ℝ) ≤ P.T) (hvalue : 2 * zetaLinePerronError c ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaLinePerronConstant c * P.N^c * zetaLineMomentConvolution c P.T t := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  have hne := P.active_nonempty_of_mem_ordinates ht
  have hinterval : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hscale
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : (1 : ℝ) ≤ (c+3)/2)
  have hresPower : P.N ^ 4 ≤ (1 + |t|) ^ 4 :=
    pow_le_pow_left₀ hNpos.le (by linarith [hinterval.1, le_abs_self t]) 4
  have hheightPower : P.N ^ (c+3 : ℝ) ≤ P.T ^ 2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le ((c+3)/2)) hscale 2
    have heq : (P.N ^ ((c+3)/2 : ℝ)) ^ 2 = P.N ^ (c+3 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    rwa [heq] at h
  have hres : zetaCutoffMellinConstant 4 1 * P.N ^ 4 / (1 + |t|) ^ 4 ≤
      zetaCutoffMellinConstant 4 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).2
    exact mul_le_mul_of_nonneg_left hresPower (zetaCutoffMellinConstant_pos _ _).le
  have hfar : (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c * P.N ^ (c+3 : ℝ) / P.T ^ 2 ≤
      (20*(1/(1-c)+2)) * zetaCutoffMellinConstant 4 c := by
    apply (div_le_iff₀ (pow_pos P.T_pos 2)).2
    exact mul_le_mul_of_nonneg_left hheightPower
      (mul_nonneg (by positivity) (zetaCutoffMellinConstant_pos _ _).le)
  have hpoly := (P.large t ht).trans
    (P.polynomial_norm_le_lineConvolution_and_errors hactive hne hc hc1 hinterval)
  unfold zetaLinePerronError at hvalue
  unfold zetaLinePerronConstant
  nlinarith

/-- One threshold works for all source sigma and tau parameters in the
arbitrary-line moment range. The actual exponent windows derive both
physical hypotheses of the proved Perron entry. -/
theorem exists_zetaLinePerron_uniform_threshold {c : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c < 1) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ τ δ : ℝ, 1 / 2 ≤ σ → 2 ≤ τ → δ ≤ min (1 / 4) ((1-c)/4) →
        P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaLinePerronConstant c * P.N^c * zetaLineMomentConvolution c P.T t := by
  have hevent : ∀ᶠ N : ℝ in atTop, 2 * zetaLinePerronError c ≤ N ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (eventually_ge_atTop (2 * zetaLinePerronError c))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro P hN σ τ δ hσ hτ hδ hT hV t ht
  have hδone : δ ≤ 1/4 := hδ.trans (min_le_left _ _)
  have hδgap : δ ≤ (1-c)/4 := hδ.trans (min_le_right _ _)
  apply P.line_perron_entry hc hc1 _ _ ht
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : ((c+3)/2 : ℝ) ≤ τ - δ)).trans hT
  · exact (hN₀ P.N ((le_max_right _ _).trans hN)).trans
      ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith : (1 / 4 : ℝ) ≤ σ - δ)).trans hV)


end TaoTrudgianYang2025

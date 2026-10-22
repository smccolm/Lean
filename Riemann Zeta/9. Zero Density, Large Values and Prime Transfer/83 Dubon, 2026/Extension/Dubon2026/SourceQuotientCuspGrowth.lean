import Dubon2026.SourceOriginalHolomorphicQuotient

/-! DUB-17/18 -> finite-place exhaustion -> bounded original functions
integral over C[j] -> a single discriminant power clears every cusp pole.
Native analytic factorization bounds each nonzero denominator below by
a q-parameter power. The actual finite Gamma0 quotient then bounds the
orders for every slash translate, while discriminant decay clears them.
No cusp-growth or finite-orbit bound is assumed in the final consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.
-/
namespace Dubon2026.SourceFunctionField.QuotientCuspGrowth
noncomputable section
open UpperHalfPlane Filter Function Complex
open scoped MatrixGroups Topology ModularForm Manifold Pointwise
variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem norm_qParam_lt_one' {h : ℝ} (hh : 0 < h) (τ : ℍ) : ‖Periodic.qParam h (τ : ℂ)‖ < 1 := by
  have := (Periodic.norm_qParam_lt_iff hh 0 (τ : ℂ)).mpr (by simpa using τ.im_pos)
  simpa using this

theorem exists_qParam_pow_le {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) (hf : f ≠ 0) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam h (τ : ℂ)‖ ^ n ≤ ‖f τ‖ := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hΦ : AnalyticAt ℂ (cuspFunction h f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hne : ¬ (∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0) := by
    intro hev
    apply hf
    have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
    have hball : AnalyticOnNhd ℂ (cuspFunction h f) (Metric.ball 0 1) :=
      (differentiableOn_cuspFunction_ball hh hper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f)).analyticOnNhd Metric.isOpen_ball
    have hz := hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected (Metric.mem_ball_self one_pos) hev
    ext τ
    have hq : Periodic.qParam h (τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using norm_qParam_lt_one' hh τ
    have := hz hq
    rw [eq_cuspFunction τ hh.ne' hper] at this
    simpa using this
  obtain ⟨n, φ, hφ, hφ0, hev⟩ := hΦ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨n, ‖φ 0‖ / 2, by positivity, ?_⟩
  have hlow : ∀ᶠ q in 𝓝 (0 : ℂ), ‖φ 0‖ / 2 < ‖φ q‖ :=
    hφ.continuousAt.norm.eventually_const_lt (by simpa using hφ0)
  have hq0 : Tendsto (fun τ : ℍ => Periodic.qParam h (τ : ℂ)) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty hh
  filter_upwards [hq0.eventually hlow, hq0.eventually hev] with τ h1 h2
  rw [← eq_cuspFunction τ hh.ne' hper, h2, norm_smul, norm_pow, mul_comm, sub_zero]
  gcongr

theorem exists_norm_discriminant_le :
    ∃ C : ℝ, ∀ᶠ τ : ℍ in atImInfty,
      ‖ModularForm.discriminant τ‖ ≤ C * ‖Periodic.qParam 1 (τ : ℂ)‖ := by
  have h := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos
    (by simp)
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨C, hC.mono fun τ hτ => ?_⟩
  rw [Periodic.norm_qParam]
  have : ‖Real.exp (-2 * Real.pi * τ.im / 1)‖ = Real.exp (-2 * Real.pi * (τ : ℂ).im / 1) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rfl
  rw [← this]
  exact hτ

theorem norm_qParam_one_le {N : ℝ} (hN : 1 ≤ N) (τ : ℍ) :
    ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ ‖Periodic.qParam N (τ : ℂ)‖ := by
  rw [Periodic.norm_qParam, Periodic.norm_qParam, Real.exp_le_exp, div_one]
  rw [le_div_iff₀ (by linarith)]
  have h1 : 0 ≤ 2 * Real.pi * (τ : ℂ).im := by
    have := τ.im_pos
    have : (0 : ℝ) < (τ : ℂ).im := this
    positivity
  nlinarith

theorem key_ineq {a b c d q q₁ C M D : ℝ} {n m : ℕ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hab : a * b = c) (hb : C * q ^ n ≤ b) (hc : c ≤ M) (hdq : d ≤ D * q₁) (hq₁ : q₁ ≤ q)
    (hq1 : q ≤ 1) (hq0 : 0 < q) (hq₁0 : 0 ≤ q₁) (hC : 0 < C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hnm : n ≤ m) : a * d ^ m ≤ M * D ^ m / C := by
  have h1 : a * d ^ m * C * q ^ n ≤ M * D ^ m * q ^ n :=
    calc a * d ^ m * C * q ^ n = a * d ^ m * (C * q ^ n) := by ring
      _ ≤ a * d ^ m * b := by gcongr
      _ = c * d ^ m := by rw [← hab]; ring
      _ ≤ M * d ^ m := by gcongr
      _ ≤ M * (D * q₁) ^ m := by gcongr
      _ ≤ M * (D * q) ^ m := by gcongr
      _ = M * D ^ m * q ^ m := by ring
      _ ≤ M * D ^ m * q ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0.le hq1 hnm) (by positivity)
  rw [le_div_iff₀ hC]
  exact le_of_mul_le_mul_right h1 (pow_pos hq0 n)


end
end Dubon2026.SourceFunctionField.QuotientCuspGrowth

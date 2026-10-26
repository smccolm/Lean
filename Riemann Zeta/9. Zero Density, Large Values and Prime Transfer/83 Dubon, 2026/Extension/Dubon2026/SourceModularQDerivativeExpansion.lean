import Dubon2026.SourceModularQDerivative
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> arithmetic Gamma1 realization -> Picard/H1 comparison ->
regular differential/cusp comparison -> finite-coordinate modular integral bound.
The literal analytic normalized derivative must match the existing q-Euler
derivation. Reuse native analytic power-series differentiation and the local
bounded-derivative theorem; no new norm-polynomial or Ramanujan system.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean. -/
namespace Dubon2026.SourceFunctionField.ModularQDerivative
noncomputable section
open UpperHalfPlane Complex Function
open scoped Real Manifold

theorem qExpansion_coeff_unique'
    {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    (m : ℕ) : c m = (UpperHalfPlane.qExpansion 1 f).coeff m := by
  have h1 : HasFPowerSeriesAt (UpperHalfPlane.cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hana hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (UpperHalfPlane.cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => (UpperHalfPlane.qExpansion 1 f).coeff n)) 0 := by
    simpa [UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hana.hasFPowerSeriesAt
  have h3 := h1.eq_formalMultilinearSeries h2
  have h4 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ =>
    FormalMultilinearSeries.coeff p m) h3
  simpa [FormalMultilinearSeries.coeff_ofScalars] using h4

theorem hasSum_qExpansion_normalizedDerivOfComplex
    (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) (τ : ℍ) :
    HasSum
      (fun m : ℕ => ((m : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff m) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (Derivative.normalizedDerivOfComplex F τ) := by
  have hper' : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) ((1 : ℝ) : ℂ) := by
    rwa [Complex.ofReal_one]
  set q : ℂ := Function.Periodic.qParam 1 (τ : ℂ) with hq_def
  have hq : ‖q‖ < 1 := norm_qParam_one_lt_one τ
  have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper' hhol hbdd
  have hsum : ∀ σ : ℍ, HasSum
      (fun m : ℕ => (UpperHalfPlane.qExpansion 1 F).coeff m •
        Function.Periodic.qParam 1 (σ : ℂ) ^ m) (F σ) :=
    UpperHalfPlane.hasSum_qExpansion one_pos hper' hhol hbdd
  have hball : HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction 1 F)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun m => (UpperHalfPlane.qExpansion 1 F).coeff m)) 0 1 :=
    UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos han hsum
  have hballD : HasFPowerSeriesOnBall (fderiv ℂ (UpperHalfPlane.cuspFunction 1 F))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun m => (UpperHalfPlane.qExpansion 1 F).coeff m)).derivSeries 0 1 := hball.fderiv
  have hqmem : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe, mem_ball_zero_iff]
    simpa using hq
  have h1 : HasSum
      (fun n : ℕ => (FormalMultilinearSeries.ofScalars ℂ
        (fun m => (UpperHalfPlane.qExpansion 1 F).coeff m)).derivSeries n (fun _ => q))
      (fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q) := by
    have h0 := hballD.hasSum hqmem
    simpa using h0
  have h2 : HasSum
      (fun n : ℕ => ((FormalMultilinearSeries.ofScalars ℂ
        (fun m => (UpperHalfPlane.qExpansion 1 F).coeff m)).derivSeries n (fun _ => q)) q)
      (fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q q) :=
    h1.mapL (ContinuousLinearMap.apply ℂ ℂ q)
  have hterm : ∀ n : ℕ,
      ((FormalMultilinearSeries.ofScalars ℂ
        (fun m => (UpperHalfPlane.qExpansion 1 F).coeff m)).derivSeries n (fun _ => q)) q =
        (((n + 1 : ℕ) : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff (n + 1)) • q ^ (n + 1) := by
    intro n
    rw [FormalMultilinearSeries.derivSeries_apply_diag,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, FormalMultilinearSeries.coeff_ofScalars]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hfd : fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q q =
      q * deriv (UpperHalfPlane.cuspFunction 1 F) q := by
    have h9 : fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q q =
        fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q (q • 1) := by norm_num
    have h10 : (fderiv ℂ (UpperHalfPlane.cuspFunction 1 F) q) 1 =
        deriv (UpperHalfPlane.cuspFunction 1 F) q := rfl
    rw [h9, ContinuousLinearMap.map_smul, smul_eq_mul, h10]
  have h3 : HasSum
      (fun n : ℕ => (((n + 1 : ℕ) : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff (n + 1)) •
        q ^ (n + 1)) (q * deriv (UpperHalfPlane.cuspFunction 1 F) q) := by
    have h2' := h2
    simp only [hterm] at h2'
    rw [← hfd]
    exact h2'
  have h5 : HasSum
      (fun m : ℕ => ((m : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff m) • q ^ m)
      ((q * deriv (UpperHalfPlane.cuspFunction 1 F) q) + ∑ i ∈ Finset.range 1,
        ((i : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff i) • q ^ i) :=
    (hasSum_nat_add_iff 1).mp h3
  rw [normalizedDerivOfComplex_eq_qParam_mul_deriv F hper hhol hbdd τ]
  simpa using h5

theorem qExpansion_coeff_normalizedDerivOfComplex
    (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex F)).coeff m =
      (m : ℂ) * (UpperHalfPlane.qExpansion 1 F).coeff m := by
  have hperD : Function.Periodic
      (Derivative.normalizedDerivOfComplex F ∘ UpperHalfPlane.ofComplex) ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]
    exact periodic_normalizedDerivOfComplex F hper
  have hholD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Derivative.normalizedDerivOfComplex F) :=
    Derivative.normalizedDerivOfComplex_mdifferentiable hhol
  have hbddD : UpperHalfPlane.IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex F) :=
    JMultiplicity.isBoundedAtImInfty_D hhol hbdd
  have hanD : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (Derivative.normalizedDerivOfComplex F)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperD hholD hbddD
  exact (qExpansion_coeff_unique' hanD
    (hasSum_qExpansion_normalizedDerivOfComplex F hper hhol hbdd) m).symm

theorem coe_qExpansion_normalizedDerivOfComplex
    (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ((UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex F) : PowerSeries ℂ) :
        LaurentSeries ℂ) =
      SourceDifferential.qEuler ℂ
        ((UpperHalfPlane.qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by
  ext k
  rw [SourceDifferential.qEuler_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
      qExpansion_coeff_normalizedDerivOfComplex F hper hhol hbdd k]
    simp
  · simp only [PowerSeries.coeff_coe, if_pos hk, mul_zero]

end
end Dubon2026.SourceFunctionField.ModularQDerivative

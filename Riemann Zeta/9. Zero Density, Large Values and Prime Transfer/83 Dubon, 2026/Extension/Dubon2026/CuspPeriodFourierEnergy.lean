import Dubon2026.CuspFourierEnergy

/-! # Exact Fourier energy for actual cusp forms with arbitrary positive periods -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- The actual q-disc restriction of a cusp form at its specified positive period. -/
def cuspPeriodCircleFunction {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h r : ℝ) (z : UnitAddCircle) : ℂ :=
  cuspFunction h f ((r : ℂ) * fourier 1 z)

/-- The actual period-h q-expansion converges on every circle inside its q-disc. -/
theorem hasSum_cuspPeriodCircleFunction {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h r : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hr : 0 ≤ r) (hr1 : r < 1) (z : UnitAddCircle) :
    HasSum (fun n => ((qExpansion h f).coeff n * (r : ℂ) ^ n) * fourier (n : ℤ) z)
      (cuspPeriodCircleFunction f h r z) := by
  letI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hq : ‖(r : ℂ) * fourier 1 z‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      fourier_apply, Circle.norm_coe, mul_one] using hr1
  simpa only [cuspPeriodCircleFunction, smul_eq_mul, mul_pow,
    circle_fourier_pow, mul_one, mul_assoc] using
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hq

/-- The actual period-h Fourier coefficients are absolutely summable after every strict radial damping. -/
theorem summable_norm_cuspPeriodCircleCoefficients {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h r : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖(qExpansion h f).coeff n * (r : ℂ) ^ n‖) := by
  have ht := (hasSum_cuspPeriodCircleFunction f hh hΓ hr hr1 0).summable.norm
  simpa only [fourier_eval_zero, mul_one] using ht

/-- Parseval applies to the actual period-h q-expansion on every strict circle. -/
theorem hasSum_cuspPeriodCircleEnergy {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h r : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => ‖(qExpansion h f).coeff n‖ ^ 2 * r ^ (2 * n))
      (∫ z : UnitAddCircle, ‖cuspPeriodCircleFunction f h r z‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have ht := hasSum_norm_sq_fourier_nat (summable_norm_cuspPeriodCircleCoefficients f hh hΓ hr hr1)
    (hasSum_cuspPeriodCircleFunction f hh hΓ hr hr1)
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_pow, ← pow_mul, Nat.mul_comm] using ht

/-- The exact period-h horizontal parameter retains the reciprocal width in the exponential damping. -/
theorem qParam_scaled_horizontal {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    Function.Periodic.qParam h (((h * x : ℝ) : ℂ) + y * Complex.I) =
      (Real.exp (-2 * Real.pi * y / h) : ℂ) * fourier 1 (x : UnitAddCircle) := by
  rw [Function.Periodic.qParam, fourier_coe_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [div_one, mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr hh]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

/-- The actual q-disc circle is exactly the cusp function on its width-h horizontal period. -/
theorem cuspPeriodCircleFunction_horizontal {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    cuspPeriodCircleFunction f h (Real.exp (-2 * Real.pi * y / h)) (x : UnitAddCircle) =
      f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩ := by
  rw [cuspPeriodCircleFunction, ← qParam_scaled_horizontal hh.ne']
  exact UpperHalfPlane.eq_cuspFunction
    (⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) hh.ne'
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)

/-- The literal period-h Fourier squares equal the normalized horizontal energy, with the true cusp width in every exponent. -/
theorem hasSum_cusp_period_horizontal_energy {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖(qExpansion h f).coeff n‖ ^ 2 *
      Real.exp (-4 * Real.pi * n * y / h))
      (∫ x in (0 : ℝ)..1, ‖f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) := by
  have hr1 : Real.exp (-2 * Real.pi * y / h) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hh)
  have ht := hasSum_cuspPeriodCircleEnergy f hh hΓ (Real.exp_pos _).le hr1
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at ht
  simp only [inv_one, one_smul, zero_add] at ht
  simp_rw [cuspPeriodCircleFunction_horizontal f hh hΓ _ hy] at ht
  convert ht using 1
  funext n
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end
end Dubon2026

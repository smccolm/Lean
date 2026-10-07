import Dubon2026.FourierNormSeries
import Dubon2026.CuspCoefficients

/-! # Actual cusp-form Fourier energy on a horizontal period -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The actual cusp function on a circle of radius r in its q-disc. -/
def cuspCircleFunction {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (r : ℝ) (z : UnitAddCircle) : ℂ :=
  cuspFunction 1 f ((r : ℂ) * fourier 1 z)

theorem hasSum_cuspCircleFunction {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (z : UnitAddCircle) :
    HasSum (fun n => (cuspCoefficients f n * (r : ℂ) ^ n) * fourier (n : ℤ) z)
      (cuspCircleFunction f r z) := by
  have hp : (1 : ℝ) ∈ (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  letI : Fact (IsCusp OnePoint.infty (Gamma0 Q : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hq : ‖(r : ℂ) * fourier 1 z‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      fourier_apply, Circle.norm_coe, mul_one] using hr1
  simpa only [cuspCoefficients, cuspCircleFunction, smul_eq_mul, mul_pow,
    circle_fourier_pow, mul_one, mul_assoc] using
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt zero_lt_one
      (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hq

theorem summable_norm_cuspCircleCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖cuspCoefficients f n * (r : ℂ) ^ n‖) := by
  have hh := (hasSum_cuspCircleFunction f hr hr1 0).summable.norm
  simpa only [fourier_eval_zero, mul_one] using hh

theorem hasSum_cuspCircleEnergy {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => ‖cuspCoefficients f n‖ ^ 2 * r ^ (2 * n))
      (∫ z : UnitAddCircle, ‖cuspCircleFunction f r z‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_norm_sq_fourier_nat (summable_norm_cuspCircleCoefficients f hr hr1)
    (hasSum_cuspCircleFunction f hr hr1)
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_pow, ← pow_mul, Nat.mul_comm] using hh

theorem qParam_horizontal_period (x y : ℝ) :
    Function.Periodic.qParam 1 ((x : ℂ) + y * Complex.I) =
      (Real.exp (-2 * Real.pi * y) : ℂ) * fourier 1 (x : UnitAddCircle) := by
  rw [Function.Periodic.qParam, fourier_coe_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [div_one, mul_one]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem cuspCircleFunction_horizontal {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    cuspCircleFunction f (Real.exp (-2 * Real.pi * y)) (x : UnitAddCircle) =
      f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ := by
  have hp : (1 : ℝ) ∈ (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  rw [cuspCircleFunction, ← qParam_horizontal_period]
  exact UpperHalfPlane.eq_cuspFunction (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) one_ne_zero
    (SlashInvariantFormClass.periodic_comp_ofComplex f hp)

/-- Parseval on the literal horizontal period of the actual cusp form. -/
theorem hasSum_cusp_horizontal_energy {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖cuspCoefficients f n‖ ^ 2 *
      Real.exp (-4 * Real.pi * n * y))
      (∫ x in (0 : ℝ)..1, ‖f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) := by
  have hr1 : Real.exp (-2 * Real.pi * y) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hh := hasSum_cuspCircleEnergy f (Real.exp_pos _).le hr1
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at hh
  simp only [inv_one, one_smul, zero_add] at hh
  simp_rw [cuspCircleFunction_horizontal f _ hy] at hh
  convert hh using 1
  funext n
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end
end Dubon2026

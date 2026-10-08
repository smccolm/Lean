import Dubon2026.CuspPeriodFourierEnergy
import Dubon2026.CuspFourierCoefficients
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Genuine Fourier extraction and vanishing constant terms at every positive cusp period -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane MeasureTheory

/-- Each actual period-h Fourier mode is exactly its original q-expansion coefficient. -/
theorem cuspPeriodCircleFunction_fourierCoeff_nat {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h r : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    fourierCoeff (cuspPeriodCircleFunction f h r) (n : ℤ) =
      (qExpansion h f).coeff n * (r : ℂ) ^ n := by
  rw [fourierCoeff_of_hasSum_nat (summable_norm_cuspPeriodCircleCoefficients f hh hΓ hr hr1)
    (hasSum_cuspPeriodCircleFunction f hh hΓ hr hr1)]
  simp

/-- The genuine constant circle integral vanishes for every positive strict cusp period. -/
theorem cuspPeriodCircleFunction_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h r : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ z : UnitAddCircle, cuspPeriodCircleFunction f h r z ∂AddCircle.haarAddCircle) = 0 := by
  have ht := cuspPeriodCircleFunction_fourierCoeff_nat f hh hΓ hr hr1 0
  simpa [fourierCoeff, CuspFormClass.qExpansion_coeff_zero f hh hΓ] using ht

/-- Every original cusp form has zero average on its literal width-h horizontal period. -/
theorem cusp_period_horizontal_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩) = 0 := by
  have hr1 : Real.exp (-2 * Real.pi * y / h) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hh)
  have ht := cuspPeriodCircleFunction_integral_zero f hh hΓ (Real.exp_pos _).le hr1
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at ht
  simp only [inv_one, one_smul, zero_add] at ht
  simpa only [cuspPeriodCircleFunction_horizontal f hh hΓ _ hy] using ht

/-- The literal horizontal cusp average vanishes with every real starting offset. -/
theorem cusp_period_horizontal_shift_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (t : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      f ⟨(((h * x + t : ℝ)) : ℂ) + y * Complex.I, by simpa using hy⟩) = 0 := by
  let F : ℝ → ℂ := fun x => f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩
  have hp : Function.Periodic F 1 := by
    intro x
    dsimp only [F]
    rw [← cuspPeriodCircleFunction_horizontal f hh hΓ _ hy,
      ← cuspPeriodCircleFunction_horizontal f hh hΓ _ hy, AddCircle.coe_add_period]
  have he (x : ℝ) :
      f ⟨(((h * x + t : ℝ)) : ℂ) + y * Complex.I, by simpa using hy⟩ = F (x + t / h) := by
    congr 1
    apply UpperHalfPlane.ext
    dsimp only [F]
    congr 1
    field_simp [hh.ne']
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right]
  have hi := hp.intervalIntegral_add_eq (t / h) 0
  simp only [zero_add] at hi
  rw [zero_add, add_comm 1, hi]
  exact cusp_period_horizontal_integral_zero f hh hΓ hy

end
end Dubon2026

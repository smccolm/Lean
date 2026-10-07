import Dubon2026.CuspPeriodFourierEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Exact horizontal energy averaging over a common integral cusp period -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- Averaging a continuous one-periodic function over any positive integral number of periods preserves its exact normalized integral. -/
theorem integral_unit_comp_nat_periodic {F : ℝ → ℝ} (hF : Function.Periodic F 1)
    (hc : Continuous F) {N : ℕ} (hN : 0 < N) :
    (∫ x in (0 : ℝ)..1, F ((N : ℝ) * x)) = ∫ x in (0 : ℝ)..1, F x := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  have hi := hF.intervalIntegral_add_zsmul_eq (N : ℤ) 0 (fun a b => hc.intervalIntegrable a b)
  simp only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] at hi
  rw [intervalIntegral.integral_comp_mul_left F hN0, mul_zero, mul_one, hi, smul_eq_mul,
    inv_mul_cancel_left₀ hN0]

/-- An actual finite family of width-N cusp forms has a literal Fourier-square expansion for its one-periodic aggregate horizontal energy. -/
theorem hasSum_cusp_common_period_energy {ι : Type*} [Fintype ι]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ι → CuspForm Γ k)
    {N : ℕ} (hN : 0 < N) (hΓ : (N : ℝ) ∈ Γ.strictPeriods) {y : ℝ} (hy : 0 < y)
    (hp : Function.Periodic (fun x : ℝ => ∑ i : ι,
      ‖f i ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) 1) :
    HasSum (fun n : ℕ => (∑ i : ι, ‖(qExpansion (N : ℝ) (f i)).coeff n‖ ^ 2) *
      Real.exp (-4 * Real.pi * n * y / N))
      (∫ x in (0 : ℝ)..1, ∑ i : ι, ‖f i ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc (i : ι) : Continuous (fun x : ℝ => f i ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩) :=
    (ModularFormClass.continuous (f i)).comp
      ((Complex.continuous_ofReal.add continuous_const).upperHalfPlaneMk (fun _ => by simpa using hy))
  have ha : Continuous (fun x : ℝ => ∑ i : ι,
      ‖f i ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => (hc i).norm.pow 2)
  have hi := integral_unit_comp_nat_periodic hp ha hN
  have hs := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_cusp_period_horizontal_energy (f i) hNR hΓ hy)
  convert hs using 1
  · funext n
    rw [Finset.sum_mul]
  · rw [← hi, intervalIntegral.integral_finsetSum]
    intro i _
    exact (((hc i).comp (continuous_const.mul continuous_id)).norm.pow 2).intervalIntegrable _ _

end
end Dubon2026

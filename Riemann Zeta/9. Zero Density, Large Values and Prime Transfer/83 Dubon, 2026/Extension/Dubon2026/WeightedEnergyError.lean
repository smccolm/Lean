import Dubon2026.WeightedEnergyAbel
import Dubon2026.PowerIntegralAsymptotics

/-! # Explicit weighted remainders from a cumulative square-sum error bound -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- The exact contribution of the linear Rankin–Selberg main term to Abel summation. -/
def weightedEnergyMain (c : ℝ) (N : ℕ) (σ : ℝ) : ℝ :=
  c * (N : ℝ) ^ (1 - 2 * σ) +
    2 * σ * c * ∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ)

theorem integrableOn_power_Icc_one (N : ℕ) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ r) (Icc 1 (N : ℝ)) := by
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  exact (Real.continuousAt_rpow_const x r (Or.inl (by linarith [hx.1]))).continuousWithinAt

theorem mul_power_sub_one {x r : ℝ} (hx : 0 < x) : x * x ^ (r - 1) = x ^ r := by
  rw [mul_comm, ← Real.rpow_add_one hx.ne']
  congr 1
  ring

theorem coefficientEnergy_sub_main (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (σ c : ℝ) :
    coefficientEnergy a N σ - weightedEnergyMain c N σ =
      (squareSummatory a N - c * N) * (N : ℝ) ^ (-2 * σ) +
        2 * σ * ∫ x in Ioc (1 : ℝ) N,
          (squareSummatory a x - c * x) * x ^ (-2 * σ - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hA := (squareSummatory_integrable_power a N (-2 * σ - 1)).mono_set Ioc_subset_Icc_self
  have hP := ((integrableOn_power_Icc_one N (-2 * σ)).mono_set Ioc_subset_Icc_self).const_mul c
  have hint : (∫ x in Ioc (1 : ℝ) N,
      (squareSummatory a x - c * x) * x ^ (-2 * σ - 1)) =
      (∫ x in Ioc (1 : ℝ) N, squareSummatory a x * x ^ (-2 * σ - 1)) -
        c * ∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ) := by
    calc
      _ = ∫ x in Ioc (1 : ℝ) N,
          squareSummatory a x * x ^ (-2 * σ - 1) - c * x ^ (-2 * σ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        dsimp only
        rw [sub_mul, mul_assoc, mul_power_sub_one (by linarith [hx.1] : 0 < x)]
      _ = _ := by rw [integral_sub hA hP, integral_const_mul]
  rw [hint, coefficientEnergy_abel a hN, weightedEnergyMain]
  have he : (N : ℝ) * (N : ℝ) ^ (-2 * σ) = (N : ℝ) ^ (1 - 2 * σ) := by
    rw [mul_comm, ← Real.rpow_add_one hN0.ne']
    congr 1
    ring
  rw [← he]
  ring

/-- A literal bound on A(x)-cx produces the source's two weighted error terms. -/
theorem weighted_energy_error_bound {a : ℕ → ℂ} {c C β : ℝ}
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β)
    {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    |coefficientEnergy a N σ - weightedEnergyMain c N σ| ≤
      C * ((N : ℝ) ^ (β - 2 * σ) +
        2 * |σ| * ∫ x in Ioc (1 : ℝ) N, x ^ (β - 2 * σ - 1)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hterm : |(squareSummatory a N - c * N) * (N : ℝ) ^ (-2 * σ)| ≤
      C * (N : ℝ) ^ (β - 2 * σ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
    calc
      _ ≤ (C * (N : ℝ) ^ β) * (N : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right (he N (by exact_mod_cast hN))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; congr 2; ring
  have hib := ((integrableOn_power_Icc_one N (β - 2 * σ - 1)).mono_set Ioc_subset_Icc_self).const_mul C
  have hint : |∫ x in Ioc (1 : ℝ) N,
      (squareSummatory a x - c * x) * x ^ (-2 * σ - 1)| ≤
        C * ∫ x in Ioc (1 : ℝ) N, x ^ (β - 2 * σ - 1) := by
    rw [← integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hib
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (C * x ^ β) * x ^ (-2 * σ - 1) :=
        mul_le_mul_of_nonneg_right (he x hx.1.le) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
  rw [coefficientEnergy_sub_main a hN]
  apply (abs_add_le _ _).trans
  rw [abs_mul (2 * σ), abs_mul (2 : ℝ) σ, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hh := add_le_add hterm (mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 2 * |σ|))
  nlinarith [hh]

end

end Dubon2026

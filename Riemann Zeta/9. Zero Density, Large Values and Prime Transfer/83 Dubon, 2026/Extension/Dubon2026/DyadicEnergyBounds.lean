import Dubon2026.ComparablePowerWeights
import Dubon2026.PotentialPointwise

/-! # Compact-uniform energy bounds for the actual isolated prime sum of zeta coefficients -/

namespace Dubon2026

open Filter Set

/-- Multiplicative exponential bounds give a genuine logarithmic error bound. -/
theorem abs_log_sub_log_le_of_exp_bounds {X Y D : ℝ} (hX : 0 < X)
    (hlo : Real.exp (-D) * X ≤ Y) (hhi : Y ≤ Real.exp D * X) :
    0 < Y ∧ |Real.log Y - Real.log X| ≤ D := by
  have hY : 0 < Y := (mul_pos (Real.exp_pos _) hX).trans_le hlo
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hX) hlo
  have hu := Real.log_le_log hY hhi
  rw [Real.log_mul (Real.exp_pos _).ne' hX.ne', Real.log_exp] at hl hu
  exact ⟨hY, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem isolatedPrimeEnergy_one_bounds {N : ℕ} (hN : 1 ≤ N) {σ M : ℝ} (hσ : |σ| ≤ M) :
    Real.exp (-(2 * M * Real.log 2)) * ((dyadicPrimes N).card : ℝ) * (N : ℝ) ^ (-2 * σ) ≤
      isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ ∧
    isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ ≤
      Real.exp (2 * M * Real.log 2) * ((dyadicPrimes N).card : ℝ) * (N : ℝ) ^ (-2 * σ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hs : |-2 * σ| ≤ 2 * M := by
    rw [abs_mul]
    norm_num
    linarith
  have hb (p : ℕ) (hp : p ∈ dyadicPrimes N) :
      Real.exp (-(2 * M * Real.log 2)) * (N : ℝ) ^ (-2 * σ) ≤ (p : ℝ) ^ (-2 * σ) ∧
      (p : ℝ) ^ (-2 * σ) ≤ Real.exp (2 * M * Real.log 2) * (N : ℝ) ^ (-2 * σ) := by
    have hp' := mem_dyadicPrimes.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
    have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.2.2
    have hh := real_power_ratio_bounds hp0 hNpos (by linarith) (by linarith [hp'.2.1]) hs
    exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)).mp hh.1,
      (div_le_iff₀ (Real.rpow_pos_of_pos hNpos _)).mp hh.2⟩
  have hl := Finset.sum_le_sum (s := dyadicPrimes N) (fun p hp => (hb p hp).1)
  have hu := Finset.sum_le_sum (s := dyadicPrimes N) (fun p hp => (hb p hp).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at hl hu
  simp only [isolatedPrimeEnergy, norm_one, one_pow, one_mul]
  constructor
  · nlinarith [hl]
  · nlinarith [hu]

theorem isolatedPrimeEnergy_one_log_error {N : ℕ} (hN : 1 ≤ N)
    (hcard : 0 < (dyadicPrimes N).card) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ) -
      (Real.log (dyadicPrimes N).card - 2 * σ * Real.log N)| ≤ 2 * M * Real.log 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcpos : (0 : ℝ) < (dyadicPrimes N).card := by exact_mod_cast hcard
  have hb := isolatedPrimeEnergy_one_bounds hN hσ
  have hh := abs_log_sub_log_le_of_exp_bounds
    (mul_pos hcpos (Real.rpow_pos_of_pos hNpos (-2 * σ)))
    (by simpa only [mul_assoc] using hb.1) (by simpa only [mul_assoc] using hb.2)
  rw [Real.log_mul hcpos.ne' (Real.rpow_pos_of_pos hNpos _).ne', Real.log_rpow hNpos] at hh
  have he : -2 * σ * Real.log N = -(2 * σ * Real.log N) := by ring
  simpa only [he, sub_eq_add_neg, mul_assoc] using hh.2

end Dubon2026

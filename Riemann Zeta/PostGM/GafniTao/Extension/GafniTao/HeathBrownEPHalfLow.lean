import GafniTao.HeathBrownEPHalfBlock
import GafniTao.FordShiftedWeylRange

/-!
# The low logarithmic range of the coefficient-one-half estimate

For `2 ≤ tau ≤ 5/2`, the frozen A/B-process estimate is stronger than the
coefficient-one-half logarithmic saving.  This file proves the exact bridge
between its zero-shift phase and Pintz's Dirichlet block, and performs the
scale calculation without changing either source object.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's unweighted block is exactly the zero-shift Ford block. -/
theorem pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
    {N R : ℕ} (t : ℝ) (hN : 0 < N) :
    pintz2023ExponentialBlock N R t =
      fordShiftedExponentialSum N R 0 t := by
  unfold pintz2023ExponentialBlock fordShiftedExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hphase :
      fordShiftedLogPhase n 0 t =
        unitaryPhase (logarithmicPhase t n) := by
    unfold fordShiftedLogPhase unitaryPhase logarithmicPhase
    simp only [add_zero, Complex.ofReal_neg, Complex.ofReal_mul]
    congr 1
    ring
  rw [hphase, unitaryPhase_logarithmicPhase_eq_cpow t n hnPos]

/-- The literal A/B-process estimate at the physical height `N^tau`. -/
theorem norm_pintz2023ExponentialBlock_le_AB_log_power
    {N R : ℕ} {tau : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 2 ≤ tau) (htauHigh : tau ≤ 5 / 2) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      90 * (N : ℝ) ^ ((tau + 3) / 6) := by
  have hNPos : 0 < N := by omega
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hNPos
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNt : (N : ℝ) ≤ (N : ℝ) ^ tau := by
    have h := Real.rpow_le_rpow_of_exponent_le hNOne
      (by linarith : (1 : ℝ) ≤ tau)
    simpa only [Real.rpow_one] using h
  have hN2t : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ tau := by
    have h := Real.rpow_le_rpow_of_exponent_le hNOne htauLow
    rw [← Real.rpow_natCast]
    exact h
  have htN3 : (N : ℝ) ^ tau ≤ (N : ℝ) ^ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le hNOne
      (by linarith : tau ≤ (3 : ℝ))
    rw [← Real.rpow_natCast]
    exact h
  have hraw := ford_shifted_weyl_above_square
    hN hNR hR (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 1 by norm_num) hNt hN2t htN3
  let A : ℝ := ((N + 1 : ℕ) : ℝ)
  let Y : ℝ := fordCubeRoot ((N : ℝ) ^ tau)
  let Z : ℝ := (N : ℝ) ^ ((tau + 3) / 6)
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp only [A]
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hY : Y = (N : ℝ) ^ (tau / 3) := by
    dsimp only [Y]
    exact fordCubeRoot_rpow hNReal
  have hprod :
      (N : ℝ) * (N : ℝ) ^ (tau / 3) = Z ^ 2 := by
    dsimp only [Z]
    calc
      (N : ℝ) * (N : ℝ) ^ (tau / 3) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (tau / 3) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ (1 + tau / 3) :=
        (Real.rpow_add hNReal _ _).symm
      _ = (N : ℝ) ^ (((tau + 3) / 6) * 2) := by ring_nf
      _ = ((N : ℝ) ^ ((tau + 3) / 6)) ^ (2 : ℝ) :=
        Real.rpow_mul hNReal.le _ _
      _ = ((N : ℝ) ^ ((tau + 3) / 6)) ^ 2 :=
        Real.rpow_natCast _ 2
  have hinside : 4 * A * Y ≤ 9 * Z ^ 2 := by
    rw [hY]
    have hmul := mul_le_mul_of_nonneg_right hAle
      (Real.rpow_nonneg hNReal.le (tau / 3))
    calc
      4 * A * (N : ℝ) ^ (tau / 3) ≤
          4 * (2 * (N : ℝ) * (N : ℝ) ^ (tau / 3)) := by
            nlinarith
      _ = 8 * ((N : ℝ) * (N : ℝ) ^ (tau / 3)) := by ring
      _ = 8 * Z ^ 2 := by rw [hprod]
      _ ≤ 9 * Z ^ 2 := by nlinarith [sq_nonneg Z]
  have hsqrt : Real.sqrt (4 * A * Y) ≤ 3 * Z := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith⟩
  have hsqrt' :
      Real.sqrt
          (4 * (((N + 1 : ℕ) : ℝ) + 0) *
            fordCubeRoot ((N : ℝ) ^ tau)) ≤
        3 * (N : ℝ) ^ ((tau + 3) / 6) := by
    simpa only [A, Y, Z, add_zero] using hsqrt
  rw [pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
    ((N : ℝ) ^ tau) hNPos]
  exact hraw.trans (by nlinarith)

/-- Coefficient-one-half saving in the complete low logarithmic range. -/
theorem norm_pintz2023ExponentialBlock_le_half_low
    {N R : ℕ} {tau epsilon : ℝ}
    (hN : 1024 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (htauLow : 2 ≤ tau) (htauHigh : tau ≤ 5 / 2)
    (hepsilon : 0 < epsilon) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      90 * (N : ℝ) ^ (1 - 1 / (2 * tau ^ 2) + epsilon) := by
  have hraw := norm_pintz2023ExponentialBlock_le_AB_log_power
    hN hNR hR htauLow htauHigh
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hexponent :
      (tau + 3) / 6 ≤ 1 - 1 / (2 * tau ^ 2) + epsilon := by
    have hsave := heathBrown_half_AB_range htauLow htauHigh
    calc
      (tau + 3) / 6 = 1 + (tau - 3) / 6 := by ring
      _ ≤ 1 + (-1 / (2 * tau ^ 2)) + epsilon := by linarith
      _ = 1 - 1 / (2 * tau ^ 2) + epsilon := by ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hNOne hexponent
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

#print axioms pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
#print axioms norm_pintz2023ExponentialBlock_le_AB_log_power
#print axioms norm_pintz2023ExponentialBlock_le_half_low

end

end GafniTao

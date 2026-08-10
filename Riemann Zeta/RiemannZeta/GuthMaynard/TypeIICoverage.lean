import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.TypeIIContour

open Complex
open scoped ArithmeticFunction.Moebius BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- Below the real Möbius cutoff, the truncated divisor set is the full
positive-divisor set. -/
theorem detectorDivisors_eq_divisors_of_le {n : ℕ} {T : ℝ}
    (hn : 0 < n) (hnCut : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) :
    detectorDivisors n T = n.divisors := by
  unfold detectorDivisors
  apply Finset.filter_eq_self.mpr
  intro d hd
  have hdNat : d ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)
  exact (by exact_mod_cast hdNat : (d : ℝ) ≤ n) |>.trans hnCut

/-- Möbius inversion identifies the unsmoothed detector coefficient with the
Dirichlet identity throughout the cancelled initial range. -/
theorem mobius_sum_eq_ite_of_le {n : ℕ} {T : ℝ}
    (hn : 0 < n) (hnCut : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) :
    mobius_sum n T = if n = 1 then 1 else 0 := by
  rw [mobius_sum, detectorDivisors_eq_divisors_of_le hn hnCut]
  calc
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) =
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          ArithmeticFunction.zeta) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      simp only [ArithmeticFunction.intCoe_apply]
    _ = (1 : ArithmeticFunction ℂ) n := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

/-- The natural cutoff was deliberately defined as one past the floor of the
source's real cutoff, so membership below it is exactly the range in which
Möbius cancellation is valid. -/
theorem mobius_sum_eq_ite_of_lt_detectorCutoff {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hn : 0 < n) (hnCut : n < detectorCutoff T) :
    mobius_sum n T = if n = 1 then 1 else 0 := by
  have hCutNonneg : 0 ≤ 2 * T ^ (1 / 100 : ℝ) := by positivity
  have hnFloor : n ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ := by
    rw [detectorCutoff] at hnCut
    omega
  exact mobius_sum_eq_ite_of_le hn
    ((Nat.le_floor_iff hCutNonneg).mp hnFloor)

/-- The constant coefficient in the smoothed detector is exactly the expected
`exp (-1/Y)` contribution. -/
theorem detectorCoeff_one (T : ℝ) (hT : 1 ≤ T) :
    detectorCoeff 1 T = Real.exp (-(1 : ℝ) / T ^ (1 / 2 : ℝ)) := by
  have hCut : 1 < detectorCutoff T := by
    rw [detectorCutoff]
    have hTwo : (2 : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
      have hPow : 1 ≤ T ^ (1 / 100 : ℝ) := Real.one_le_rpow hT (by norm_num)
      nlinarith
    have hFloor : 2 ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ :=
      (Nat.le_floor_iff (by positivity)).mpr hTwo
    omega
  rw [detectorCoeff, mobius_sum_eq_ite_of_lt_detectorCutoff
    (zero_le_one.trans hT) (by norm_num) hCut]
  norm_num

/-- All nonconstant coefficients before the Möbius cutoff vanish exactly. -/
theorem detectorCoeff_eq_zero_of_lt_cutoff {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hn : 2 ≤ n) (hnCut : n < detectorCutoff T) :
    detectorCoeff n T = 0 := by
  rw [detectorCoeff,
    mobius_sum_eq_ite_of_lt_detectorCutoff hT (by omega) hnCut,
    if_neg (by omega), zero_mul]

end RiemannZeta.GuthMaynard

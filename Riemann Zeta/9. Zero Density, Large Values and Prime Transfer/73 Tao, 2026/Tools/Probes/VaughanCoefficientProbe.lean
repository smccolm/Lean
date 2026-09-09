import Tao2026.VaughanIdentity

open ArithmeticFunction
open scoped Moebius zeta

#check Nat.sum_divisorsAntidiagonal
#check Nat.sum_divisorsAntidiagonal'
#check ArithmeticFunction.coe_mul_zeta_apply
#check ArithmeticFunction.coe_zeta_mul_apply
#check ArithmeticFunction.abs_moebius_le_one
#check Finset.abs_sum_le_sum_abs
#check Finset.sum_le_sum
#check ArithmeticFunction.mul_apply
#check Real.strictMonoOn_log

namespace Tao2026

theorem probe_tail_apply {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (X n : ℕ) :
    arithmeticFunctionTail f X n = if X < n then f n else 0 := by
  by_cases h : n ≤ X
  · rw [arithmeticFunctionTail_apply_of_le f h]
    simp [Nat.not_lt.mpr h]
  · have hlt : X < n := Nat.lt_of_not_ge h
    rw [arithmeticFunctionTail_apply_of_lt f hlt]
    simp [hlt]

theorem probe_tail_vonMangoldt_nonneg (V n : ℕ) :
    0 ≤ arithmeticFunctionTail Λ V n := by
  rw [probe_tail_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem probe_tail_vonMangoldt_le (V n : ℕ) :
    arithmeticFunctionTail Λ V n ≤ Λ n := by
  rw [probe_tail_apply]
  split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

theorem probe_typeII (V n : ℕ) :
    0 ≤ (arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ)) n ∧
      (arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ)) n ≤ Real.log n := by
  rw [coe_mul_zeta_apply]
  constructor
  · exact Finset.sum_nonneg fun i _hi => probe_tail_vonMangoldt_nonneg V i
  · rw [← vonMangoldt_sum]
    exact Finset.sum_le_sum fun i _hi => probe_tail_vonMangoldt_le V i

theorem probe_cutoff_moebius_abs_le (U n : ℕ) :
    |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  by_cases h : n ≤ U
  · rw [arithmeticFunctionCutoff_apply, if_pos h]
    calc
      |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (1 : ℝ) := by exact_mod_cast (abs_moebius_le_one (n := n))
  · simp [arithmeticFunctionCutoff_apply, h]

theorem probe_cutoff_vonMangoldt_nonneg (V n : ℕ) :
    0 ≤ arithmeticFunctionCutoff Λ V n := by
  rw [arithmeticFunctionCutoff_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem probe_cutoff_vonMangoldt_le (V n : ℕ) :
    arithmeticFunctionCutoff Λ V n ≤ Λ n := by
  rw [arithmeticFunctionCutoff_apply]
  split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

theorem probe_typeI_prime (U V n : ℕ) :
    |(arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
        arithmeticFunctionCutoff Λ V) n| ≤ Real.log n := by
  rw [mul_apply]
  calc
    |∑ x ∈ n.divisorsAntidiagonal,
        arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1 *
          arithmeticFunctionCutoff Λ V x.2| ≤
        ∑ x ∈ n.divisorsAntidiagonal,
          |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1 *
            arithmeticFunctionCutoff Λ V x.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, Λ x.2 := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [abs_mul, abs_of_nonneg (probe_cutoff_vonMangoldt_nonneg V x.2)]
      calc
        |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1| *
            arithmeticFunctionCutoff Λ V x.2 ≤
            1 * arithmeticFunctionCutoff Λ V x.2 := by
          exact mul_le_mul_of_nonneg_right (probe_cutoff_moebius_abs_le U x.1)
            (probe_cutoff_vonMangoldt_nonneg V x.2)
        _ ≤ Λ x.2 := by simpa using probe_cutoff_vonMangoldt_le V x.2
    _ = ∑ i ∈ n.divisors, Λ i := by
      exact Nat.sum_divisorsAntidiagonal' (fun _ y => Λ y)
    _ = Real.log n := vonMangoldt_sum

theorem probe_log_nat_mono {n P : ℕ} (hn : 1 ≤ n) (hP : n ≤ P) :
    Real.log n ≤ Real.log P := by
  exact Real.strictMonoOn_log.monotoneOn
    (show (0 : ℝ) < (n : ℝ) by exact_mod_cast (Nat.zero_lt_of_lt hn))
    (show (0 : ℝ) < (P : ℝ) by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hn) hP))
    (by exact_mod_cast hP)

theorem probe_typeI_prime_at_scale (U V n P : ℕ) (hn : 1 ≤ n) (hP : n ≤ P) :
    |(arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
        arithmeticFunctionCutoff Λ V) n| ≤ Real.log P :=
  (probe_typeI_prime U V n).trans (probe_log_nat_mono hn hP)

theorem probe_tail_moebius_abs_le (U n : ℕ) :
    |arithmeticFunctionTail (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  rw [probe_tail_apply]
  split_ifs
  · calc
      |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (1 : ℝ) := by exact_mod_cast (abs_moebius_le_one (n := n))
  · simp

theorem probe_typeII_abs_at_scale (V n P : ℕ) (hn : 1 ≤ n) (hP : n ≤ P) :
    |(arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ)) n| ≤ Real.log P := by
  rw [abs_of_nonneg (probe_typeII V n).1]
  exact (probe_typeII V n).2.trans (probe_log_nat_mono hn hP)

theorem probe_typeI_prime_eq_zero_of_mul_lt
    (U V n : ℕ) (hn : U * V < n) :
    (arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
        arithmeticFunctionCutoff Λ V) n = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨hprod, _hn0⟩
  by_cases hU : x.1 ≤ U
  · have hnotV : ¬x.2 ≤ V := by
      intro hV
      exact (Nat.not_le_of_lt hn) (hprod ▸ Nat.mul_le_mul hU hV)
    simp [arithmeticFunctionCutoff_apply, hnotV]
  · simp [arithmeticFunctionCutoff_apply, hU]

theorem probe_typeII_eq_zero_of_le (V n : ℕ) (hn : n ≤ V) :
    (arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ)) n = 0 := by
  rw [coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply arithmeticFunctionTail_apply_of_le
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, hn0⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).trans hn

end Tao2026

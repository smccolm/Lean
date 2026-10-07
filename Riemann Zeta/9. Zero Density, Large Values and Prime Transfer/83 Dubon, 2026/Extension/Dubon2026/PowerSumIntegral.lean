import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Integral comparison for every real power on the positive natural interval -/

namespace Dubon2026

open MeasureTheory Set

theorem power_sum_Ico_endpoint {N : ℕ} (hN : 1 ≤ N) (r : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) =
      (∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ r) + (N : ℝ) ^ r := by
  simpa only [Finset.Ico_add_one_right_eq_Icc] using
    Finset.sum_Ico_succ_top hN (fun n : ℕ => (n : ℝ) ^ r)

theorem power_sum_shift_endpoint {N : ℕ} (hN : 1 ≤ N) (r : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) =
      1 + ∑ n ∈ Finset.Ico 1 N, ((n + 1 : ℕ) : ℝ) ^ r := by
  have hs := Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ r) 1 N 1
  rw [hs]
  have he : Finset.Icc 1 N = insert 1 (Finset.Ico (1 + 1) (N + 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_insert (by simp)]
  simp only [Nat.cast_one, Real.one_rpow]

theorem abs_power_sum_sub_integral {N : ℕ} (hN : 1 ≤ N) (r : ℝ) :
    |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) - ∫ x in (1 : ℝ)..N, x ^ r| ≤
      1 + (N : ℝ) ^ r := by
  have he := power_sum_Ico_endpoint hN r
  have hs := power_sum_shift_endpoint hN r
  have hp := Real.rpow_nonneg (Nat.cast_nonneg N) r
  by_cases hr : 0 ≤ r
  · have hm : MonotoneOn (fun x : ℝ => x ^ r) (Icc (1 : ℕ) N) := by
      intro x hx y _ hxy
      have hx1 : (1 : ℝ) ≤ x := by simpa only [Nat.cast_one] using hx.1
      exact Real.rpow_le_rpow (zero_le_one.trans hx1) hxy hr
    have hl := hm.sum_le_integral_Ico hN
    have hu := hm.integral_le_sum_Ico hN
    norm_num only [Nat.cast_one] at hl hu
    apply abs_le.mpr
    constructor <;> linarith
  · have hm : AntitoneOn (fun x : ℝ => x ^ r) (Icc (1 : ℕ) N) := by
      intro x hx y _ hxy
      have hx1 : (1 : ℝ) ≤ x := by simpa only [Nat.cast_one] using hx.1
      exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx1) hxy (le_of_not_ge hr)
    have hl := hm.sum_le_integral_Ico hN
    have hu := hm.integral_le_sum_Ico hN
    norm_num only [Nat.cast_one] at hl hu
    apply abs_le.mpr
    constructor <;> linarith

theorem abs_power_sum_sub_main {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : -1 < r) :
    |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) - (N : ℝ) ^ (r + 1) / (r + 1)| ≤
      1 + (N : ℝ) ^ r + 1 / (r + 1) := by
  have hh := abs_power_sum_sub_integral hN r
  rw [integral_rpow (Or.inl hr), Real.one_rpow] at hh
  have he : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) - (N : ℝ) ^ (r + 1) / (r + 1) =
      ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) - ((N : ℝ) ^ (r + 1) - 1) / (r + 1)) -
        1 / (r + 1) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_of_pos (div_pos zero_lt_one (by linarith) : 0 < 1 / (r + 1))]
  exact add_le_add hh le_rfl

end Dubon2026

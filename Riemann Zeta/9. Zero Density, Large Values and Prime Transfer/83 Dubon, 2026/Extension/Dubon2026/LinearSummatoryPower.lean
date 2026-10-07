import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Dubon2026.PowerIntegralAsymptotics

/-! # Exact Abel formulas for nonnegative sequences with a linear summatory bound -/

namespace Dubon2026

open Set MeasureTheory

noncomputable section

/-- A genuine zero initial coefficient identifies the zero-based and positive-index finite sums. -/
theorem sum_Icc_zero_eq_positive {c : ℕ → ℝ} (hc : c 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, c n) = ∑ n ∈ Finset.Icc 1 N, c n := by
  have he : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [he, Finset.sum_insert (by simp), hc, zero_add]

/-- The power-weighted actual cumulative sum is integrable on each compact positive interval. -/
theorem linearSummatory_integrable_power (c : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (p : ℝ) :
    IntegrableOn (fun x : ℝ => (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ p) (Icc a b) := by
  have hc : ContinuousOn (fun x : ℝ => x ^ p) (Icc a b) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x p (Or.inl (ha.trans_le hx.1).ne')).continuousWithinAt
  simpa only [mul_comm] using integrableOn_mul_sum_Icc c ha.le hc.integrableOn_Icc

/-- The literal finite power sum has its exact Abel integral, with a genuine zero coefficient at index zero. -/
theorem linearPowerSum_abel (c : ℕ → ℝ) (hc0 : c 0 = 0) (N : ℕ) (p : ℝ) :
    (∑ n ∈ Finset.Icc 0 N, c n * (n : ℝ) ^ (-p)) =
      (∑ n ∈ Finset.Icc 0 N, c n) * (N : ℝ) ^ (-p) +
        p * ∫ x in Ioc (1 : ℝ) N, (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ (-p - 1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (1 : ℝ) N) :
      HasDerivAt (fun y : ℝ => y ^ (-p)) ((-p) * x ^ (-p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))
  have hc : ContinuousOn (fun x : ℝ => (-p) * x ^ (-p - 1)) (Icc (1 : ℝ) N) := by
    apply continuousOn_const.mul
    intro x hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hh := sum_mul_eq_sub_integral_mul₀' c hc0 N (fun x hx => (hd x hx).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun x hx => (hd x hx).deriv.symm) measurableSet_Icc)
  have hs : (∑ n ∈ Finset.Icc 0 N, (n : ℝ) ^ (-p) * c n) =
      ∑ n ∈ Finset.Icc 0 N, c n * (n : ℝ) ^ (-p) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : (∫ x in Ioc (1 : ℝ) N, deriv (fun y : ℝ => y ^ (-p)) x *
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) =
      (-p) * ∫ x in Ioc (1 : ℝ) N, (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ (-p - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(hd x ⟨hx.1.le, hx.2⟩).deriv]
    ring
  rw [hs, hi] at hh
  linear_combination hh

/-- The exact Abel formula also retains the lower endpoint of every genuine power-weighted tail. -/
theorem linearPowerTail_abel (c : ℕ → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (p : ℝ) :
    (∑ n ∈ Finset.Ioc N M, c n * (n : ℝ) ^ (-p)) =
      (∑ n ∈ Finset.Icc 0 M, c n) * (M : ℝ) ^ (-p) -
        (∑ n ∈ Finset.Icc 0 N, c n) * (N : ℝ) ^ (-p) +
          p * ∫ x in Ioc (N : ℝ) M, (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ (-p - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd (x : ℝ) (hx : x ∈ Icc (N : ℝ) M) :
      HasDerivAt (fun y : ℝ => y ^ (-p)) ((-p) * x ^ (-p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (hN0.trans_le hx.1).ne')
  have hc : ContinuousOn (fun x : ℝ => (-p) * x ^ (-p - 1)) (Icc (N : ℝ) M) := by
    apply continuousOn_const.mul
    intro x hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl (hN0.trans_le hx.1).ne')).continuousWithinAt
  have hh := sum_mul_eq_sub_sub_integral_mul' c hNM (fun x hx => (hd x hx).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun x hx => (hd x hx).deriv.symm) measurableSet_Icc)
  have hs : (∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-p) * c n) =
      ∑ n ∈ Finset.Ioc N M, c n * (n : ℝ) ^ (-p) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : (∫ x in Ioc (N : ℝ) M, deriv (fun y : ℝ => y ^ (-p)) x *
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) =
      (-p) * ∫ x in Ioc (N : ℝ) M, (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) * x ^ (-p - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(hd x ⟨hx.1.le, hx.2⟩).deriv]
    ring
  rw [hs, hi] at hh
  linear_combination hh

end
end Dubon2026

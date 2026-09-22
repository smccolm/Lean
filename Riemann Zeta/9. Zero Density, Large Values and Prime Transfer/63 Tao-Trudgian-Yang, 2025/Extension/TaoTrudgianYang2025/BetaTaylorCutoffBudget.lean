import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder
import TaoTrudgianYang2025.BetaBufferedJets

/-!
# Cancellation of shrinking-cutoff losses by matched finite Taylor jets

The order-i cutoff loss h^(-i) is paired with the actual order-(n-i)
Taylor remainder. The powers cancel term by term in Leibniz's formula.
The bound concerns the original function and its constructed polynomial.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem abs_iteratedDeriv_cutoff_taylor_remainder_le
    {χ f : ℝ → ℝ} {a x h A M : ℝ} {n Q : ℕ}
    (hn : n ≤ Q) (hh : 0 < h) (hx : |x-a| ≤ h)
    (hχ : ContDiffAt ℝ n χ x)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y)
    (hχb : ∀ i ≤ n, |iteratedDeriv i χ x| ≤ A*(h⁻¹)^i)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) :
    |iteratedDeriv n (fun y => χ y*(f y-finiteTaylorPolynomial f Q a y)) x| ≤
      (2 : ℝ)^n*A*M*h^(Q+1-n) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb a left_mem_uIcc)
  have hA : 0 ≤ A := by
    have hz := hχb 0 (Nat.zero_le n)
    simp only [pow_zero,mul_one] at hz
    exact (abs_nonneg _).trans hz
  have hN : (n : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  have hR : ContDiffAt ℝ n (fun y => f y-finiteTaylorPolynomial f Q a y) x :=
    ((hf x right_mem_uIcc).sub (finiteTaylorPolynomial_contDiff f Q a).contDiffAt).of_le hN
  rw [iteratedDeriv_fun_mul hχ hR]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1),
        |(n.choose i : ℝ)*iteratedDeriv i χ x*
          iteratedDeriv (n-i) (fun y => f y-finiteTaylorPolynomial f Q a y) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(A*M*h^(Q+1-n)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hij : n-i ≤ Q := (Nat.sub_le _ _).trans hn
      have hrem := abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le hij hf hb
      have hrem' : |iteratedDeriv (n-i) (fun y => f y-finiteTaylorPolynomial f Q a y) x| ≤
          M*h^(Q+1-(n-i)) :=
        hrem.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hx _) hM)
      have hprod := mul_le_mul (hχb i hin) hrem' (abs_nonneg _)
        (mul_nonneg hA (pow_nonneg (inv_nonneg.mpr hh.le) i))
      have hcancel : (h⁻¹)^i*h^(Q+1-(n-i)) = h^(Q+1-n) := by
        rw [show Q+1-(n-i) = i+(Q+1-n) by omega,pow_add,
          ← mul_assoc,← mul_pow,inv_mul_cancel₀ hh.ne',one_pow,one_mul]
      rw [abs_mul,abs_mul,Nat.abs_cast]
      calc
        _ = (n.choose i : ℝ)*(|iteratedDeriv i χ x| *
            |iteratedDeriv (n-i) (fun y => f y-finiteTaylorPolynomial f Q a y) x|) := by ring
        _ ≤ (n.choose i : ℝ)*((A*(h⁻¹)^i)*(M*h^(Q+1-(n-i)))) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
        _ = (n.choose i : ℝ)*(A*M*((h⁻¹)^i*h^(Q+1-(n-i)))) := by ring
        _ = _ := by rw [hcancel]
    _ = (2 : ℝ)^n*A*M*h^(Q+1-n) := by
      rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
      ring

end TaoTrudgianYang2025

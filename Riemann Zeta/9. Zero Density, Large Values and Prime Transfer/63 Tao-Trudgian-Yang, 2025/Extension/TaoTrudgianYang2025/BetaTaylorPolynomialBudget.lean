import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder

/-!
# Finite Taylor-polynomial budgets on a fixed observation window

The anchor may move. Its original finite jet bounds and a bound on the
observation distance give uniform polynomial and derivative estimates.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem abs_finiteTaylorPolynomial_le
    {f : ℝ → ℝ} {a x D M : ℝ} (Q : ℕ)
    (hD : 1 ≤ D) (hx : |x-a| ≤ D)
    (hb : ∀ j ≤ Q, |iteratedDeriv j f a| ≤ M) :
    |finiteTaylorPolynomial f Q a x| ≤ (Q+1 : ℕ)*D^Q*M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 (Nat.zero_le Q))
  rw [finiteTaylorPolynomial,taylor_within_apply]
  calc
    _ ≤ ∑ j ∈ Finset.range (Q+1),
        |((j.factorial : ℝ)⁻¹*(x-a)^j)*iteratedDeriv j f a| := by
      simpa only [smul_eq_mul,iteratedDerivWithin_univ] using
        Finset.abs_sum_le_sum_abs (fun j => ((j.factorial : ℝ)⁻¹*(x-a)^j)*
          iteratedDeriv j f a) (Finset.range (Q+1))
    _ ≤ ∑ _j ∈ Finset.range (Q+1), D^Q*M := by
      apply Finset.sum_le_sum
      intro j hj
      have hjQ : j ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
      have hinv : (j.factorial : ℝ)⁻¹ ≤ 1 :=
        (inv_le_one₀ (Nat.cast_pos.mpr (Nat.factorial_pos j))).mpr hfac
      have hp : |x-a|^j ≤ D^Q :=
        (pow_le_pow_left₀ (abs_nonneg _) hx j).trans (pow_le_pow_right₀ hD hjQ)
      rw [abs_mul,abs_mul,abs_inv,Nat.abs_cast,abs_pow]
      have hc : (j.factorial : ℝ)⁻¹*|x-a|^j ≤ D^Q := by
        exact (mul_le_mul hinv hp (pow_nonneg (abs_nonneg _) j) zero_le_one).trans_eq (one_mul _)
      exact mul_le_mul hc (hb j hjQ) (abs_nonneg _) (pow_nonneg (zero_le_one.trans hD) Q)
    _ = _ := by rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem abs_iteratedDeriv_finiteTaylorPolynomial_le
    {f : ℝ → ℝ} {a x D M : ℝ} {Q n : ℕ}
    (hn : n ≤ Q) (hD : 1 ≤ D) (hx : |x-a| ≤ D)
    (hb : ∀ j ≤ Q, |iteratedDeriv j f a| ≤ M) :
    |iteratedDeriv n (finiteTaylorPolynomial f Q a) x| ≤ (Q+1 : ℕ)*D^Q*M := by
  rw [iteratedDeriv_finiteTaylorPolynomial f a hn]
  have h := abs_finiteTaylorPolynomial_le (f := iteratedDeriv n f) (M := M) (Q-n) hD hx ?_
  · have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 (Nat.zero_le Q))
    have hcount : ((Q-n+1 : ℕ) : ℝ) ≤ ((Q+1 : ℕ) : ℝ) := by exact_mod_cast (show Q-n+1 ≤ Q+1 by omega)
    have hp := pow_le_pow_right₀ hD (Nat.sub_le Q n)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hcount hp (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)) hM)
  · intro j hj
    rw [iteratedDeriv_real_comp_order]
    exact hb (j+n) (by omega)

end TaoTrudgianYang2025

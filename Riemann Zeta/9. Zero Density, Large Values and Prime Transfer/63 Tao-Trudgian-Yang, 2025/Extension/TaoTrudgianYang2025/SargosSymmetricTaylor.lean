import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder

/-! Actual symmetric degree-five Taylor cancellation and its sixth-order error. -/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

def sargosSymmetricRemainder (f : ℝ → ℝ) (n m : ℝ) : ℝ :=
  f (m+n)+f (m-n)-2*f m-n^2*iteratedDeriv 2 f m-(n^4/12)*iteratedDeriv 4 f m

theorem sargos_symmetric_taylor_polynomial (f : ℝ → ℝ) (m n : ℝ) :
    finiteTaylorPolynomial f 5 m (m+n)+finiteTaylorPolynomial f 5 m (m-n) =
      2*f m+n^2*iteratedDeriv 2 f m+(n^4/12)*iteratedDeriv 4 f m := by
  simp only [finiteTaylorPolynomial,taylor_within_apply,Nat.reduceAdd,
    Finset.sum_range_succ,Finset.sum_range_zero,iteratedDerivWithin_univ,smul_eq_mul]
  norm_num [iteratedDeriv_zero,Nat.factorial]
  ring

theorem sargosSymmetricRemainder_eq_errors (f : ℝ → ℝ) (m n : ℝ) :
    sargosSymmetricRemainder f n m =
      (f (m+n)-finiteTaylorPolynomial f 5 m (m+n))+
      (f (m-n)-finiteTaylorPolynomial f 5 m (m-n)) := by
  have h := sargos_symmetric_taylor_polynomial f m n
  unfold sargosSymmetricRemainder
  linarith only [h]

theorem sargos_symmetric_taylor_identity (f : ℝ → ℝ) (m n : ℝ) :
    f (m+n)+f (m-n) =
      2*f m+n^2*iteratedDeriv 2 f m+(n^4/12)*iteratedDeriv 4 f m+
        sargosSymmetricRemainder f n m := by
  unfold sargosSymmetricRemainder
  ring

theorem abs_sargosSymmetricRemainder_le {f : ℝ → ℝ} {m n B : ℝ}
    (hn : 0 ≤ n)
    (hf : ∀ x ∈ Icc (m-n) (m+n), ContDiffAt ℝ ∞ f x)
    (hB : ∀ x ∈ Icc (m-n) (m+n), |iteratedDeriv 6 f x| ≤ B) :
    |sargosSymmetricRemainder f n m| ≤ B*n^6/360 := by
  have hp : uIcc m (m+n) ⊆ Icc (m-n) (m+n) := by
    rw [uIcc_of_le (by linarith)]
    intro x hx
    exact ⟨by linarith [hx.1],hx.2⟩
  have hm : uIcc m (m-n) ⊆ Icc (m-n) (m+n) := by
    rw [uIcc_of_ge (by linarith)]
    intro x hx
    exact ⟨hx.1,by linarith [hx.2]⟩
  have hplus := abs_finiteTaylorPolynomial_remainder_le (f := f) (a := m) (x := m+n)
    (M := B) 5 (fun x hx => hf x (hp hx)) (fun x hx => hB x (hp hx))
  have hminus := abs_finiteTaylorPolynomial_remainder_le (f := f) (a := m) (x := m-n)
    (M := B) 5 (fun x hx => hf x (hm hx)) (fun x hx => hB x (hm hx))
  rw [show m+n-m=n by ring,abs_of_nonneg hn] at hplus
  rw [show m-n-m = -n by ring,abs_neg,abs_of_nonneg hn] at hminus
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at hplus hminus
  rw [sargosSymmetricRemainder_eq_errors]
  exact (abs_add_le _ _).trans (by linarith only [hplus,hminus])

end TaoTrudgianYang2025

import TaoTrudgianYang2025.BetaTaylorGlobal
import Mathlib.Analysis.Calculus.Taylor

/-!
# Exact finite Taylor jets for a moving-endpoint extension

The polynomial is globally smooth independently of exterior behavior of
the original function. Its finite jet matches the actual derivatives at
the anchor. Quantitative remainder estimates are separate obligations.
-/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def finiteTaylorPolynomial (f : ℝ → ℝ) (Q : ℕ) (a : ℝ) : ℝ → ℝ :=
  taylorWithinEval f Q univ a

theorem finiteTaylorPolynomial_contDiff (f : ℝ → ℝ) (Q : ℕ) (a : ℝ) :
    ContDiff ℝ ∞ (finiteTaylorPolynomial f Q a) := by
  change ContDiff ℝ ∞ (fun x => taylorWithinEval f Q univ a x)
  simp_rw [taylor_within_apply]
  fun_prop

theorem finiteTaylorPolynomial_succ_hasDerivAt
    (f : ℝ → ℝ) (Q : ℕ) (a x : ℝ) :
    HasDerivAt (finiteTaylorPolynomial f (Q+1) a)
      (finiteTaylorPolynomial (deriv f) Q a x) x := by
  simpa only [finiteTaylorPolynomial,derivWithin_univ] using
    (hasDerivAt_taylorWithinEval_succ (x₀ := a) (x := x) (s := univ) f Q)

theorem iteratedDeriv_finiteTaylorPolynomial
    (f : ℝ → ℝ) (a : ℝ) {n Q : ℕ} (hn : n ≤ Q) (x : ℝ) :
    iteratedDeriv n (finiteTaylorPolynomial f Q a) x =
      finiteTaylorPolynomial (iteratedDeriv n f) (Q-n) a x := by
  induction n generalizing f Q with
  | zero => simp only [iteratedDeriv_zero,Nat.sub_zero]
  | succ n ih =>
      cases Q with
      | zero => omega
      | succ Q =>
          rw [iteratedDeriv_succ']
          have he : deriv (finiteTaylorPolynomial f (Q+1) a) =
              finiteTaylorPolynomial (deriv f) Q a := by
            funext y
            exact (finiteTaylorPolynomial_succ_hasDerivAt f Q a y).deriv
          rw [he,ih (deriv f) (by omega)]
          simp only [Nat.succ_sub_succ_eq_sub,iteratedDeriv_succ']

theorem finiteTaylorPolynomial_matches_jet
    (f : ℝ → ℝ) (a : ℝ) {n Q : ℕ} (hn : n ≤ Q) :
    iteratedDeriv n (finiteTaylorPolynomial f Q a) a = iteratedDeriv n f a := by
  rw [iteratedDeriv_finiteTaylorPolynomial f a hn]
  exact taylorWithinEval_self _ _ _ _

end TaoTrudgianYang2025

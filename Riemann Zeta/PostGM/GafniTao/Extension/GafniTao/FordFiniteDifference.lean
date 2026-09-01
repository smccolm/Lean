import GafniTao.FordPolynomialSystem
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Ford Section 3: the type-raising finite difference

Ford passes from a system of type `(d,T)` to one of type `(d+1,yT)` by
replacing each polynomial `p(X)` by `p(X+y)-p(X)`.  This file proves the
degree and leading-coefficient calculation underlying that step.
-/

open Polynomial

namespace GafniTao

noncomputable section

/-- The literal polynomial `p(X+y)-p(X)`. -/
def fordFiniteDifference (y : ℚ) (p : ℚ[X]) : ℚ[X] :=
  p.taylor y - p

@[simp] theorem fordFiniteDifference_eval (y x : ℚ) (p : ℚ[X]) :
    (fordFiniteDifference y p).eval x = p.eval (x + y) - p.eval x := by
  simp [fordFiniteDifference, taylor_eval]

theorem fordFiniteDifference_coeff
    {n : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = n + 1) (y : ℚ) :
    (fordFiniteDifference y p).coeff n =
      ((n + 1 : ℕ) : ℚ) * p.leadingCoeff * y := by
  let h := p.hasseDeriv n
  have hhdeg : h.natDegree ≤ 1 := by
    dsimp [h]
    simpa [hdeg] using p.natDegree_hasseDeriv_le n
  have heq : h = C (h.coeff 1) * X + C (h.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hhdeg
  rw [fordFiniteDifference, coeff_sub, taylor_coeff]
  change h.eval y - p.coeff n = _
  rw [heq]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  change ((p.hasseDeriv n).coeff 1 * y + (p.hasseDeriv n).coeff 0) -
      p.coeff n = _
  rw [hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add]
  rw [show 1 + n = n + 1 by omega, Nat.choose_succ_self_right]
  rw [show p.coeff (n + 1) = p.leadingCoeff by
    rw [← hdeg, coeff_natDegree], Nat.choose_self]
  norm_num

theorem fordFiniteDifference_natDegree_le
    {n : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = n + 1) (y : ℚ) :
    (fordFiniteDifference y p).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold fordFiniteDifference
  rw [coeff_sub, taylor_coeff]
  have hhN : (p.hasseDeriv N).natDegree ≤ 0 := by
    refine (p.natDegree_hasseDeriv_le N).trans ?_
    rw [hdeg]
    omega
  rw [eq_C_of_natDegree_le_zero hhN, eval_C, hasseDeriv_coeff]
  simp

theorem fordFiniteDifference_natDegree
    {n : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = n + 1)
    (hlc : p.leadingCoeff ≠ 0) {y : ℚ} (hy : y ≠ 0) :
    (fordFiniteDifference y p).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (fordFiniteDifference_natDegree_le hdeg y)
  rw [fordFiniteDifference_coeff hdeg]
  exact mul_ne_zero (mul_ne_zero (by positivity) hlc) hy

theorem fordFiniteDifference_leadingCoeff
    {n : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = n + 1)
    (hlc : p.leadingCoeff ≠ 0) {y : ℚ} (hy : y ≠ 0) :
    (fordFiniteDifference y p).leadingCoeff =
      ((n + 1 : ℕ) : ℚ) * p.leadingCoeff * y := by
  rw [leadingCoeff, fordFiniteDifference_natDegree hdeg hlc hy,
    fordFiniteDifference_coeff hdeg]

/-- Ford's type-raising operation.  As in the use in Lemma 3.3, the first
`d+1` coordinates are set identically to zero and the remaining coordinates
are replaced by their finite differences. -/
def fordDifferenceSystem
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hT : 0 < T) (y : ℕ) (hy : 0 < y) :
    FordPolynomialSystem k (d + 1) (y * T) where
  poly j := if (j : ℕ) + 1 ≤ d + 1 then 0
    else fordFiniteDifference (y : ℚ) (ψ.poly j)
  twoMultiplicity := ψ.twoMultiplicity
  zero_below j hj := by simp [hj]
  degree_above j hj := by
    rw [if_neg (not_le_of_gt hj)]
    have hjd : d < (j : ℕ) + 1 := by omega
    have hold : (ψ.poly j).natDegree =
        ((j : ℕ) + 1 - (d + 1)) + 1 := by
      rw [ψ.degree_above j hjd]
      omega
    apply fordFiniteDifference_natDegree hold
    · rw [ψ.leadingCoeff_above j hjd]
      positivity
    · exact_mod_cast (ne_of_gt hy)
  leadingCoeff_above j hj := by
    rw [if_neg (not_le_of_gt hj)]
    have hjd : d < (j : ℕ) + 1 := by omega
    have hold : (ψ.poly j).natDegree =
        ((j : ℕ) + 1 - (d + 1)) + 1 := by
      rw [ψ.degree_above j hjd]
      omega
    rw [fordFiniteDifference_leadingCoeff hold (by
      rw [ψ.leadingCoeff_above j hjd]
      positivity) (by exact_mod_cast (ne_of_gt hy)),
      ψ.leadingCoeff_above j hjd]
    have hfac : ((j : ℕ) + 1 - d).factorial =
        ((j : ℕ) + 1 - d) * (((j : ℕ) + 1 - (d + 1)).factorial) := by
      have hs : (j : ℕ) + 1 - d = ((j : ℕ) + 1 - (d + 1)) + 1 := by omega
      rw [hs, Nat.factorial_succ]
    rw [hfac]
    have hstep : (j : ℕ) + 1 - (d + 1) + 1 = (j : ℕ) + 1 - d := by
      omega
    rw [hstep]
    push_cast
    field_simp
    apply mul_inv_cancel₀
    apply ne_of_gt
    exact_mod_cast Nat.sub_pos_of_lt hjd

#print axioms fordFiniteDifference_eval
#print axioms fordFiniteDifference_coeff
#print axioms fordFiniteDifference_natDegree
#print axioms fordFiniteDifference_leadingCoeff
#print axioms fordDifferenceSystem

end

end GafniTao

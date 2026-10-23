import Dubon2026.SourceEllipticOddNormSpecialization

/-! Finite polynomial factorization for the explicit odd cyclic
quotient. Translated roots determine the cleared numerator; the three
two-torsion fibers then identify the quotient cubic and its discriminant.
This is the necessary algebraic step before actual-curve assembly in the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain through quotient products,
cyclic-subgroup roots, inertia census, reverse genus and good reduction.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native monic polynomial root
comparison is reused. The actual-curve hypotheses are not asserted here. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)
/-- The rational odd quotient x-coordinate away from its kernel poles. -/
noncomputable def Xv (v : K) : K := v + ∑ q ∈ S, (t q / (v - x q) + u q / (v - x q) ^ 2)

omit [DecidableEq ι] in
theorem hP_eval (v : K) : (hP S x).eval v = ∏ q ∈ S, (v - x q) := by
  rw [hP, eval_prod]
  simp

omit [DecidableEq ι] in
theorem hP_eval_ne_zero (v : K) (hv : ∀ q ∈ S, v ≠ x q) : (hP S x).eval v ≠ 0 := by
  rw [hP_eval]
  exact prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (hv q hq)

theorem AP_eval (v : K) (hv : ∀ q ∈ S, v ≠ x q) :
    (AP S x t u).eval v = (hP S x).eval v ^ 2 * Xv S x t u v := by
  have hh : ∀ q ∈ S, (hP S x).eval v = (v - x q) * ∏ q' ∈ S.erase q, (v - x q') := by
    intro q hq
    rw [hP_eval, mul_prod_erase S (fun q' => v - x q') hq]
  rw [AP, Xv]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_finsetSum, eval_prod, eval_sub, eval_C]
  rw [mul_add, mul_sum, mul_comm]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  have hvq : v - x q ≠ 0 := sub_ne_zero.mpr (hv q hq)
  rw [hh q hq, prod_pow]
  field_simp


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

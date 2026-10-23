import Dubon2026.SourceEllipticOddNormPolynomials

/-! Characteristic-two algebra for the actual odd quotient discriminant.
The ordinary case uses the squared-coordinate norm polynomial and its two
required coefficients. The supersingular case uses the actual unchanged
a3 coefficient. These cases are required by odd quotient ellipticity,
cyclic quotient products, inertia census and modular-curve good reduction
for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2; characteristic two is not excluded.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native root bounds and the
already proved denominator degree replace duplicate general foundations. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
theorem neg_eq_self_of_two (h2 : (2 : K) = 0) (a : K) : -a = a := by
  linear_combination (-a) * h2

theorem sub_sq_of_two (h2 : (2 : K) = 0) (a b : K) : (a - b) ^ 2 = a ^ 2 - b ^ 2 := by
  linear_combination (-b * (a - b)) * h2

theorem sum_sq_of_two (h2 : (2 : K) = 0) {ι : Type*} (s : Finset ι) (f : ι → K) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, ← ih]
    linear_combination (f a * ∑ i ∈ s, f i) * h2

variable {ι : Type*} [DecidableEq ι] (I : Finset ι) (x Y : ι → K)

/-- Cleared characteristic-two quotient polynomial at squared coordinates. -/
noncomputable def BtP : K[X] :=
  ∏ i ∈ I, (X - C (x i ^ 2)) + ∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2))

omit [DecidableEq ι] in
theorem monic_prod_X_sub_C' (s : Finset ι) (g : ι → K) :
    (∏ i ∈ s, (X - C (g i))).Monic :=
  Polynomial.monic_prod_X_sub_C g s

omit [DecidableEq ι] in
theorem natDegree_prod_X_sub_C' (s : Finset ι) (g : ι → K) :
    (∏ i ∈ s, (X - C (g i))).natDegree = s.card := by
  exact Algebra.natDegree_hP s g

theorem BtP_eval (v : K) : (BtP I x).eval v
    = ∏ i ∈ I, (v - x i ^ 2) + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, (v - x i ^ 2) := by
  simp only [BtP, eval_add, eval_prod, eval_finsetSum, eval_mul, eval_sub, eval_X, eval_C]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo

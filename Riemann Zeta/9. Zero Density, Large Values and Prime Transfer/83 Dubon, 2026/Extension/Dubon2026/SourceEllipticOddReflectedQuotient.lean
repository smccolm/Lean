import Dubon2026.SourceEllipticOddPolynomialDegrees

/-! Polynomial coefficient comparison on the odd cyclic quotient
discriminant chain. The exact rational numerator and denominator are reflected
and compared modulo X^4 to recover the quotient cubic coefficients. These
calculations serve odd quotient ellipticity -> prime quotient maps/products
-> cyclic-subgroup root interpretation -> inertia census -> reverse genus
and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial reflection,
degree bounds, quotient rings and finite products are reused. The full
curve discriminant identity is not asserted by these conditional identities. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
theorem reflect_sq (a : K) : reflect 2 ((X - C a) ^ 2) = (1 - C a * X) ^ 2 := by
  have e := reflect_pow_le (X - C a) 1 2 (natDegree_X_sub_C_le' a)
  rw [mul_one] at e
  rw [e, reflect_X_sub_C]

omit [DecidableEq ι] in
omit [DecidableEq ι] in
theorem reflect_hP : reflect S.card (hP S x) = ∏ q ∈ S, (1 - C (x q) * X) := by
  have e := reflect_prod_le S (fun q => (X - C (x q) : K[X])) 1
    (fun q _ => natDegree_X_sub_C_le' _)
  rw [mul_one] at e
  rw [hP, e]
  exact prod_congr rfl fun q _ => reflect_X_sub_C _

theorem reflect_AP : reflect (2 * S.card + 1) (AP S x t u) = reflect S.card (hP S x) ^ 2
    + ∑ q ∈ S, (C (t q) * (1 - C (x q) * X) + C (u q) * X)
      * (∏ q' ∈ S.erase q, (1 - C (x q') * X) ^ 2) * X ^ 2 := by
  have hdeg_h := natDegree_hP_le S x
  have hdeg_h2 : (hP S x ^ 2).natDegree ≤ 2 * S.card :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_h)
  rw [AP, reflect_add]
  congr 1
  · rw [show 2 * S.card + 1 = 1 + 2 * S.card by ring, reflect_mul _ _ natDegree_X_le hdeg_h2,
      reflect_one_X, one_mul, reflect_pow_le _ _ 2 hdeg_h]
  · rw [reflect_sum']
    refine sum_congr rfl fun q hq => ?_
    have hk : (S.erase q).card + 1 = S.card := card_erase_add_one hq
    have e1 := reflect_mul ((C (t q) * (X - C (x q)) + C (u q)) *
        ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2) (1 : K[X])
      ((natDegree_mul_le).trans (add_le_add (natDegree_lin_le x t u q) (natDegree_Pq_le S x q)))
      (show (1 : K[X]).natDegree ≤ 2 by simp)
    rw [mul_one] at e1
    rw [show 2 * S.card + 1 = (1 + (S.erase q).card * 2) + 2 by omega, e1,
      reflect_mul _ _ (natDegree_lin_le x t u q) (natDegree_Pq_le S x q),
      reflect_prod_le (S.erase q) _ 2 (fun q' _ => (natDegree_pow_le).trans
        (by have := natDegree_X_sub_C_le' (R := K) (x q'); omega)),
      reflect_add, reflect_C_mul, reflect_X_sub_C, reflect_C, pow_one,
      show reflect 2 (1 : K[X]) = X ^ 2 by rw [← C_1, reflect_C, C_1, one_mul]]
    congr 2
    exact prod_congr rfl fun q' _ => reflect_sq _

theorem fP_eq (b₂ b₄ b₆ : K) :
    fP b₂ b₄ b₆ = C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 1 + C b₆ * X ^ 0 := by
  rw [fP, pow_one, pow_zero, mul_one]

theorem reflect_fP (b₂ b₄ b₆ : K) :
    reflect 3 (fP b₂ b₄ b₆) = C 4 + C b₂ * X + C (2 * b₄) * X ^ 2 + C b₆ * X ^ 3 := by
  rw [fP_eq]
  simp only [reflect_add, reflect_C_mul_X_pow]
  rw [revAt_le (show 3 ≤ 3 by norm_num), revAt_le (show 2 ≤ 3 by norm_num),
    revAt_le (show 1 ≤ 3 by norm_num), revAt_le (show 0 ≤ 3 by norm_num)]
  norm_num

omit [DecidableEq ι] in
theorem reflect_m (m : ι → K[X]) (b₂ b₄ b₆ b₈ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆) :
    ∀ q ∈ S, reflect 3 (m q) * (1 - C (x q) * X)
      = (C 1 * X ^ 0 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 3 - C b₈ * X ^ 4)
        - C (d q) * (C 4 * X ^ 1 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 3 + C b₆ * X ^ 4) := by
  intro q hq
  have e := congrArg (reflect 4) (hm q hq)
  rw [show (4 : ℕ) = 3 + 1 from rfl,
    reflect_mul _ _ (natDegree_m_le S x d m b₂ b₄ b₆ b₈ hm q hq) (natDegree_X_sub_C_le' _),
    reflect_X_sub_C] at e
  rw [e, reflect_sub, reflect_C_mul, fP_eq, φP,
    show (X : K[X]) ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈
      = C 1 * X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 1 - C b₈ * X ^ 0 by
        rw [C_1, one_mul, pow_one, pow_zero, mul_one]]
  simp only [reflect_add, reflect_sub, reflect_C_mul_X_pow]
  rw [revAt_le (show 4 ≤ 3 + 1 by norm_num), revAt_le (show 2 ≤ 3 + 1 by norm_num),
    revAt_le (show 1 ≤ 3 + 1 by norm_num), revAt_le (show 0 ≤ 3 + 1 by norm_num),
    revAt_le (show 3 ≤ 3 + 1 by norm_num)]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

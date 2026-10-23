import Dubon2026.SourceEllipticOddQuotientPolynomials

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
omit [DecidableEq ι] in
theorem natDegree_hP_le : (hP S x).natDegree ≤ S.card := by
  rw [hP]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul S (fun i => (X - C (x i) : K[X]).natDegree) 1
    fun i _ => natDegree_X_sub_C_le' (x i)).trans ?_
  simp

omit [DecidableEq ι] in
theorem natDegree_lin_le (q : ι) : (C (t q) * (X - C (x q)) + C (u q) : K[X]).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le' _)) (by simp)

theorem natDegree_Pq_le (q : ι) :
    (∏ q' ∈ S.erase q, (X - C (x q')) ^ 2 : K[X]).natDegree ≤ (S.erase q).card * 2 := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ S.erase q, ((X - C (x i)) ^ 2 : K[X]).natDegree ≤ ∑ _i ∈ S.erase q, 2 :=
        sum_le_sum fun i _ => (natDegree_pow_le).trans (by
          have := natDegree_X_sub_C_le' (R := K) (x i); omega)
    _ = (S.erase q).card * 2 := by simp

theorem natDegree_AP_le : (AP S x t u).natDegree ≤ 2 * S.card + 1 := by
  rw [AP]
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine (natDegree_mul_le).trans ?_
    have h2 : (hP S x ^ 2).natDegree ≤ 2 * S.card :=
      (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (natDegree_hP_le S x))
    have := natDegree_X_le (R := K)
    omega
  · refine natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
    refine (natDegree_mul_le).trans ?_
    have h1 := natDegree_lin_le x t u q
    have h2 := natDegree_Pq_le S x q
    have h3 : (S.erase q).card + 1 = S.card := card_erase_add_one hq
    omega

theorem natDegree_fP_le (b₂ b₄ b₆ : K) : (fP b₂ b₄ b₆).natDegree ≤ 3 := by
  rw [fP]
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 3 natDegree_X_le)
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
      (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · simp

theorem natDegree_φP_le (b₄ b₆ b₈ : K) : (φP b₄ b₆ b₈ : K[X]).natDegree ≤ 4 := by
  rw [φP]
  refine natDegree_sub_le_of_le' (natDegree_sub_le_of_le' (natDegree_sub_le_of_le' ?_ ?_) ?_) ?_
  · exact natDegree_pow_le_of_le 4 natDegree_X_le
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
      (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · simp

omit [DecidableEq ι] in
theorem natDegree_m_le (m : ι → K[X]) (b₂ b₄ b₆ b₈ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆) :
    ∀ q ∈ S, (m q).natDegree ≤ 3 := by
  intro q hq
  by_cases hm0 : m q = 0
  · simp [hm0]
  have hXC : (X - C (x q) : K[X]) ≠ 0 := X_sub_C_ne_zero _
  have key := congrArg natDegree (hm q hq)
  rw [natDegree_mul hm0 hXC, natDegree_X_sub_C] at key
  have : (φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆ : K[X]).natDegree ≤ 4 :=
    natDegree_sub_le_of_le' (natDegree_φP_le b₄ b₆ b₈) ((natDegree_C_mul_le _ _).trans
      ((natDegree_fP_le b₂ b₄ b₆).trans (by norm_num)))
  omega


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

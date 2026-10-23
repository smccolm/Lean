import Dubon2026.SourceEllipticOddReflectedQuotient

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
theorem reflect_diamond (m : ι → K[X]) (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆)
    (hdiamond : C 4 * AP S x t u ^ 3 + C c₂ * AP S x t u ^ 2 * hP S x ^ 2
        + C c₁ * AP S x t u * hP S x ^ 4 + C c₀ * hP S x ^ 6
        = fP b₂ b₄ b₆ * ∏ q ∈ S, m q ^ 2) :
    C 4 * reflect (2 * S.card + 1) (AP S x t u) ^ 3
        + C c₂ * X * reflect (2 * S.card + 1) (AP S x t u) ^ 2 * reflect S.card (hP S x) ^ 2
        + C c₁ * X ^ 2 * reflect (2 * S.card + 1) (AP S x t u) * reflect S.card (hP S x) ^ 4
        + C c₀ * X ^ 3 * reflect S.card (hP S x) ^ 6
      = reflect 3 (fP b₂ b₄ b₆) * ∏ q ∈ S, reflect 3 (m q) ^ 2 := by
  have hdeg_h := natDegree_hP_le S x
  have hdeg_A := natDegree_AP_le S x t u
  have hdeg_f := natDegree_fP_le (K := K) b₂ b₄ b₆
  have hdeg_m := natDegree_m_le S x d m b₂ b₄ b₆ b₈ hm
  set n := S.card with hn
  set h := hP S x with hh
  set A := AP S x t u with hA
  set f := fP b₂ b₄ b₆ with hf
  have hdeg_h2 : (h ^ 2).natDegree ≤ 2 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_h)
  have hdeg_h4 : (h ^ 4).natDegree ≤ 4 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 4 hdeg_h)
  have hdeg_h6 : (h ^ 6).natDegree ≤ 6 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 6 hdeg_h)
  have hdeg_A2 : (A ^ 2).natDegree ≤ 2 * (2 * n + 1) :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_A)
  have hdeg_A2h2 : (A ^ 2 * h ^ 2).natDegree ≤ 2 * (2 * n + 1) + 2 * n :=
    (natDegree_mul_le).trans (add_le_add hdeg_A2 hdeg_h2)
  have hdeg_Ah4 : (A * h ^ 4).natDegree ≤ (2 * n + 1) + 4 * n :=
    (natDegree_mul_le).trans (add_le_add hdeg_A hdeg_h4)
  have hdeg_m2 : ∀ q ∈ S, (m q ^ 2).natDegree ≤ 6 := fun q hq =>
    (natDegree_pow_le).trans (by have := hdeg_m q hq; omega)
  have hdeg_prod : (∏ q ∈ S, m q ^ 2).natDegree ≤ n * 6 := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ S, (m i ^ 2).natDegree ≤ ∑ _i ∈ S, 6 := sum_le_sum fun i hi => hdeg_m2 i hi
      _ = n * 6 := by simp [hn]
  have hdegC : ∀ (c : K) (k : ℕ), (C c : K[X]).natDegree ≤ k := fun c k => by simp
  have T3 : reflect (6 * n + 3) (C 4 * A ^ 3) = C 4 * reflect (2 * n + 1) A ^ 3 := by
    rw [reflect_C_mul, show 6 * n + 3 = 3 * (2 * n + 1) by ring, reflect_pow_le A _ 3 hdeg_A]
  have T2 : reflect (6 * n + 3) (C c₂ * A ^ 2 * h ^ 2)
      = C c₂ * X * reflect (2 * n + 1) A ^ 2 * reflect n h ^ 2 := by
    rw [show C c₂ * A ^ 2 * h ^ 2 = (A ^ 2 * h ^ 2) * C c₂ by ring,
      show 6 * n + 3 = (2 * (2 * n + 1) + 2 * n) + 1 by ring,
      reflect_mul _ _ hdeg_A2h2 (hdegC c₂ 1), reflect_mul _ _ hdeg_A2 hdeg_h2,
      reflect_pow_le A _ 2 hdeg_A, reflect_pow_le h _ 2 hdeg_h, reflect_C]
    ring
  have T1 : reflect (6 * n + 3) (C c₁ * A * h ^ 4)
      = C c₁ * X ^ 2 * reflect (2 * n + 1) A * reflect n h ^ 4 := by
    rw [show C c₁ * A * h ^ 4 = (A * h ^ 4) * C c₁ by ring,
      show 6 * n + 3 = ((2 * n + 1) + 4 * n) + 2 by ring,
      reflect_mul _ _ hdeg_Ah4 (hdegC c₁ 2), reflect_mul _ _ hdeg_A hdeg_h4,
      reflect_pow_le h _ 4 hdeg_h, reflect_C]
    ring
  have T0 : reflect (6 * n + 3) (C c₀ * h ^ 6) = C c₀ * X ^ 3 * reflect n h ^ 6 := by
    rw [show C c₀ * h ^ 6 = h ^ 6 * C c₀ by ring,
      reflect_mul _ _ hdeg_h6 (hdegC c₀ 3), reflect_pow_le h _ 6 hdeg_h, reflect_C]
    ring
  have TR : reflect (6 * n + 3) (f * ∏ q ∈ S, m q ^ 2)
      = reflect 3 f * ∏ q ∈ S, reflect 3 (m q) ^ 2 := by
    rw [show 6 * n + 3 = 3 + n * 6 by ring, reflect_mul _ _ hdeg_f hdeg_prod, hn,
      reflect_prod_le S _ 6 hdeg_m2]
    congr 1
    refine prod_congr rfl fun q hq => ?_
    have e := reflect_pow_le (m q) 3 2 (hdeg_m q hq)
    rw [show 2 * 3 = 6 by norm_num] at e
    exact e
  have R := congrArg (reflect (6 * n + 3)) hdiamond
  rw [reflect_add, reflect_add, reflect_add, T3, T2, T1, T0, TR] at R
  exact R


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

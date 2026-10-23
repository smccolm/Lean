import Mathlib.Algebra.Polynomial.Reverse
import Dubon2026.SourceEllipticVeluCoefficients

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
section Reflect

variable {R : Type*} [CommRing R]

theorem reflect_sum' {ι : Type*} (s : Finset ι) (p : ι → R[X]) (N : ℕ) :
    reflect N (∑ q ∈ s, p q) = ∑ q ∈ s, reflect N (p q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, reflect_add, ih]

theorem reflect_prod_le {ι : Type*} (s : Finset ι) (p : ι → R[X]) (b : ℕ)
    (hb : ∀ q ∈ s, (p q).natDegree ≤ b) :
    reflect (s.card * b) (∏ q ∈ s, p q) = ∏ q ∈ s, reflect b (p q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha,
      show (s.card + 1) * b = b + s.card * b by ring]
    have hbs : (∏ q ∈ s, p q).natDegree ≤ s.card * b := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ i ∈ s, (p i).natDegree ≤ ∑ _i ∈ s, b :=
            sum_le_sum fun i hi => hb i (mem_insert_of_mem hi)
        _ = s.card * b := by simp
    rw [reflect_mul _ _ (hb a (mem_insert_self a s)) hbs,
      ih fun q hq => hb q (mem_insert_of_mem hq)]

theorem reflect_pow_le (p : R[X]) (b k : ℕ) (hb : p.natDegree ≤ b) :
    reflect (k * b) (p ^ k) = reflect b p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, show (k + 1) * b = k * b + b by ring,
      reflect_mul _ _ ((natDegree_pow_le).trans (Nat.mul_le_mul_left k hb)) hb, ih]

theorem reflect_X_sub_C (a : R) : reflect 1 (X - C a) = 1 - C a * X := by
  rw [reflect_sub, reflect_one_X, reflect_C, pow_one]

theorem natDegree_sub_le_of_le' {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) : (p - q).natDegree ≤ n :=
  (natDegree_sub_le_of_le hp hq).trans (max_le le_rfl le_rfl)

theorem natDegree_X_sub_C_le' (a : R) : (X - C a : R[X]).natDegree ≤ 1 :=
  natDegree_sub_le_of_le' natDegree_X_le ((natDegree_C a).le.trans zero_le_one)

end Reflect

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

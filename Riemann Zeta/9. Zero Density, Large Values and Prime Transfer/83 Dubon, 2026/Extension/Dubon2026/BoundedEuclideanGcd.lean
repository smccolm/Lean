import Dubon2026.AlmostAnalyticPolynomialOperations

/-! # A bounded Euclidean algorithm computes the actual polynomial GCD -/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The Euclidean remainder recursion with an explicit finite step bound. -/
def boundedEuclideanGcd (P Q : ℝ[X]) : ℕ → ℝ[X]
  | 0 => Q
  | k + 1 => if P = 0 then Q else if P.natDegree = 0 then P else
      boundedEuclideanGcd (Q % P) P k

theorem boundedEuclideanGcd_eq (k : ℕ) (P Q : ℝ[X]) (hk : P.natDegree < k) :
    boundedEuclideanGcd P Q k = EuclideanDomain.gcd P Q := by
  induction k generalizing P Q with
  | zero => omega
  | succ k ih =>
    by_cases hp : P = 0
    · simp only [boundedEuclideanGcd, hp, if_true, EuclideanDomain.gcd_zero_left]
    · by_cases hd : P.natDegree = 0
      · simp only [boundedEuclideanGcd, if_neg hp, if_pos hd]
        apply Eq.symm
        apply EuclideanDomain.gcd_eq_left.mpr
        have hu : IsUnit P := Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hp, hd]
          rfl)
        exact hu.dvd
      · simp only [boundedEuclideanGcd, if_neg hp, if_neg hd]
        rw [ih (Q % P) P ((Polynomial.natDegree_mod_lt Q hd).trans_le
          (Nat.lt_succ_iff.mp hk)), ← EuclideanDomain.gcd_val]

theorem boundedEuclideanGcd_natDegree_le (k : ℕ) {P Q : ℝ[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) :
    (boundedEuclideanGcd P Q k).natDegree ≤ d := by
  induction k generalizing P Q with
  | zero => exact hQ
  | succ k ih =>
    simp only [boundedEuclideanGcd]
    split_ifs
    · exact hQ
    · exact hP
    · exact ih ((polynomial_natDegree_mod_le_left Q P).trans hQ) hP

theorem polynomial_gcd_eq_normalize_bounded {P Q : ℝ[X]} {d : ℕ}
    (hd : P.natDegree ≤ d) :
    gcd P Q = normalize (boundedEuclideanGcd P Q (d + 1)) := by
  rw [boundedEuclideanGcd_eq _ _ _ (Nat.lt_succ_of_le hd),
    polynomial_gcd_eq_normalize_euclidean]

end

end Dubon2026

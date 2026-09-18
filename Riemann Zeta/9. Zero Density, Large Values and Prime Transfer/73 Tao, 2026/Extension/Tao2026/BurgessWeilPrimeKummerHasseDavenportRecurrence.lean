import Tao2026.BurgessWeilPrimeKummerHasseDavenportEuler

/-!
# The Hasse--Davenport logarithmic-derivative recurrence

This file isolates the final formal-power-series calculation in the classical
monic-polynomial proof of Hasse--Davenport.  If `A` is a coefficient sequence
and `B` is its logarithmic-derivative sequence, the relation

`(n + 1) A (n + 1) = \sum_{k = 0}^n B (k + 1) A (n - k)`

determines `B`.  When `A = 1 + G X`, the solution is the signed power sequence
`B (n + 1) = (-1)^n G^(n + 1)`.

The second half applies this calculation to the genuine Hasse--Davenport
monic weight.  The preceding coefficient theorems show that its generating
series is exactly `1 + gaussSum χ ψ * X`.  Consequently, any closed-point
sequence satisfying the displayed recurrence already has the desired
Hasse--Davenport values.  The remaining finite-field task is now precisely
the construction of that recurrence from normalized irreducible factors.
-/

open scoped BigOperators

noncomputable section

namespace Tao2026

/-- The coefficient recurrence expressing `X A'(X) = B(X) A(X)`. -/
def HasseDavenportLogDerivativeRecurrence (A B : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, (n + 1 : ℂ) * A (n + 1) =
    ∑ k ∈ Finset.range (n + 1), B (k + 1) * A (n - k)

namespace HasseDavenportLogDerivativeRecurrence

/-- The logarithmic derivative of `1 + G X` has signed-power coefficients. -/
theorem signedPower
    (A B : ℕ → ℂ) (G : ℂ)
    (hA0 : A 0 = 1) (hA1 : A 1 = G)
    (hAzero : ∀ n : ℕ, 2 ≤ n → A n = 0)
    (hrec : HasseDavenportLogDerivativeRecurrence A B) (n : ℕ) :
    B (n + 1) = (-1 : ℂ) ^ n * G ^ (n + 1) := by
  induction n with
  | zero =>
      simpa [HasseDavenportLogDerivativeRecurrence, hA0, hA1] using (hrec 0).symm
  | succ n ih =>
      have hearly :
          ∑ k ∈ Finset.range n, B (k + 1) * A (n + 1 - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        rw [hAzero (n + 1 - k) (by omega), mul_zero]
      have h := hrec (n + 1)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hearly] at h
      have hsub1 : n + 1 - n = 1 := by omega
      have hsub0 : n + 1 - (n + 1) = 0 := by omega
      rw [hAzero (n + 2) (by omega), hsub1, hsub0, hA1, hA0] at h
      simp only [mul_zero, zero_add, mul_one] at h
      rw [ih] at h
      rw [pow_succ, pow_succ]
      linear_combination -h

end HasseDavenportLogDerivativeRecurrence

/-- The fixed-degree sum of the multiplicative Hasse--Davenport monic weight. -/
def hasseDavenportMonicSum
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (n : ℕ) : ℂ :=
  ∑ p : {p : Polynomial K // p.Monic ∧ p.natDegree = n},
    hasseDavenportMonicWeight χ ψ p.1

@[simp] theorem hasseDavenportMonicSum_zero
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    hasseDavenportMonicSum K χ ψ 0 = 1 := by
  let p0 : {p : Polynomial K // p.Monic ∧ p.natDegree = 0} :=
    ⟨1, Polynomial.monic_one, Polynomial.natDegree_one⟩
  letI : Unique {p : Polynomial K // p.Monic ∧ p.natDegree = 0} :=
    { default := p0
      uniq := by
        intro p
        apply Subtype.ext
        exact p.2.1.natDegree_eq_zero.mp p.2.2 }
  rw [hasseDavenportMonicSum, Fintype.sum_unique]
  change hasseDavenportMonicWeight χ ψ p0.1 = 1
  exact hasseDavenportMonicWeight_one χ ψ

@[simp] theorem hasseDavenportMonicSum_one
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    hasseDavenportMonicSum K χ ψ 1 = gaussSum χ ψ := by
  rw [hasseDavenportMonicSum]
  simp_rw [hasseDavenportMonicWeight_eq_fixedDegree χ ψ 0]
  exact sum_hasseDavenportMonicPolynomialWeight_one χ ψ

theorem hasseDavenportMonicSum_eq_zero_of_two_le
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    hasseDavenportMonicSum K χ ψ n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    exact ⟨n - 2, by omega⟩
  rw [hasseDavenportMonicSum]
  simp_rw [hasseDavenportMonicWeight_eq_fixedDegree χ ψ (m + 1)]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    sum_hasseDavenportMonicPolynomialWeight_eq_zero χ ψ hχ m

/-- Once the closed-point sequence satisfies the Euler logarithmic-derivative
recurrence, its values are exactly the signed powers required by
Hasse--Davenport. -/
theorem hasseDavenportClosedPointSequence_eq_signedGaussPower
    (K : Type*) [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1)
    (B : ℕ → ℂ)
    (hrec : HasseDavenportLogDerivativeRecurrence
      (hasseDavenportMonicSum K χ ψ) B) (n : ℕ) :
    B (n + 1) = (-1 : ℂ) ^ n * gaussSum χ ψ ^ (n + 1) := by
  apply HasseDavenportLogDerivativeRecurrence.signedPower
    (hasseDavenportMonicSum K χ ψ) B (gaussSum χ ψ)
  · simp
  · simp
  · intro m hm
    exact hasseDavenportMonicSum_eq_zero_of_two_le K χ ψ hχ m hm
  · exact hrec

end Tao2026

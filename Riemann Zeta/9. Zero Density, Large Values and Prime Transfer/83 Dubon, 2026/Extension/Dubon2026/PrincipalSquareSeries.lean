import Dubon2026.SquareLiftLSeries
import Dubon2026.Gamma0PrincipalFactor

/-! # The actual square-supported principal-character factor -/

namespace Dubon2026

noncomputable section

/-- The coprimality indicator on square roots, supported on actual natural squares. -/
def principalSquareCoefficients (Q : ℕ) : ℕ → ℂ :=
  squareLiftCoefficients (fun n => (1 : DirichletCharacter ℂ Q) n)

/-- At a square the coefficient is exactly the coprimality indicator for its root. -/
theorem principalSquareCoefficients_sq (Q n : ℕ) :
    principalSquareCoefficients Q (n ^ 2) = if Nat.Coprime n Q then 1 else 0 := by
  rw [principalSquareCoefficients, squareLiftCoefficients_sq, principalCharacter_nat_indicator]

/-- Every actual square-supported principal coefficient is zero or one. -/
theorem principalSquareCoefficients_eq_zero_or_one (Q n : ℕ) :
    principalSquareCoefficients Q n = 0 ∨ principalSquareCoefficients Q n = 1 := by
  by_cases hn : n ∈ Set.range (fun m : ℕ => m ^ 2)
  · obtain ⟨m, rfl⟩ := hn
    rw [principalSquareCoefficients_sq]
    split_ifs <;> simp
  · exact Or.inl (squareLiftCoefficients_eq_zero _ hn)

/-- The actual square-supported coefficients have nonnegative real part. -/
theorem principalSquareCoefficients_re_nonneg (Q n : ℕ) :
    0 ≤ (principalSquareCoefficients Q n).re := by
  rcases principalSquareCoefficients_eq_zero_or_one Q n with h | h <;> simp [h]

/-- The actual square-supported coefficients are real. -/
theorem principalSquareCoefficients_im (Q n : ℕ) :
    (principalSquareCoefficients Q n).im = 0 := by
  rcases principalSquareCoefficients_eq_zero_or_one Q n with h | h <;> simp [h]

/-- The actual square-supported principal series converges absolutely in Re(s)>1/2. -/
theorem principalSquare_lseriesSummable (Q : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (principalSquareCoefficients Q) s := by
  apply (lseriesSummable_squareLift_iff _ s).mpr
  apply DirichletCharacter.LSeriesSummable_of_one_lt_re
  simp only [two_mul, Complex.add_re]
  linarith

/-- The actual square-supported series is exactly the principal-character L-value at 2s. -/
theorem principalSquare_LSeries (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (principalSquareCoefficients Q) s = DirichletCharacter.LFunctionTrivChar Q (2 * s) := by
  have h2 : 1 < (2 * s).re := by simp only [two_mul, Complex.add_re]; linarith
  rw [principalSquareCoefficients, LSeries_squareLift
    (DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ Q) h2)]
  exact (DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ Q) h2).symm

end
end Dubon2026

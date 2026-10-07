import Dubon2026.PrincipalSquareSeries
import Mathlib.NumberTheory.LSeries.Injectivity

/-! # The genuine square-supported Möbius inverse of the principal factor -/

namespace Dubon2026

noncomputable section

/-- The actual principal-character twist of Möbius, supported on natural squares. -/
def moebiusSquareCoefficients (Q : ℕ) : ℕ → ℂ :=
  squareLiftCoefficients (fun n => (1 : DirichletCharacter ℂ Q) n *
    (ArithmeticFunction.moebius n : ℂ))

/-- The inverse coefficient at n² is the genuine coprime Möbius coefficient. -/
theorem moebiusSquareCoefficients_sq (Q n : ℕ) :
    moebiusSquareCoefficients Q (n ^ 2) =
      if Nat.Coprime n Q then (ArithmeticFunction.moebius n : ℂ) else 0 := by
  rw [moebiusSquareCoefficients, squareLiftCoefficients_sq, principalCharacter_nat_indicator]
  split_ifs <;> simp

/-- The square-supported inverse Dirichlet series converges absolutely in Re(s)>1/2. -/
theorem moebiusSquare_lseriesSummable (Q : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (moebiusSquareCoefficients Q) s := by
  apply (lseriesSummable_squareLift_iff _ s).mpr
  apply DirichletCharacter.LSeriesSummable_mul
  apply ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
  simp only [two_mul, Complex.add_re]
  linarith

/-- The two actual square-supported Dirichlet series are multiplicative inverses. -/
theorem principalSquare_mul_moebiusSquare_LSeries (Q : ℕ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    LSeries (principalSquareCoefficients Q) s * LSeries (moebiusSquareCoefficients Q) s = 1 := by
  have h2 : 1 < (2 * s).re := by simp only [two_mul, Complex.add_re]; linarith
  have hμ : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ Q) n *
      (ArithmeticFunction.moebius n : ℂ)) (2 * s) :=
    DirichletCharacter.LSeriesSummable_mul (1 : DirichletCharacter ℂ Q)
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h2)
  rw [principalSquareCoefficients, moebiusSquareCoefficients,
    LSeries_squareLift (DirichletCharacter.LSeriesSummable_of_one_lt_re
      (1 : DirichletCharacter ℂ Q) h2),
    LSeries_squareLift hμ]
  exact DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ Q) h2

end
end Dubon2026

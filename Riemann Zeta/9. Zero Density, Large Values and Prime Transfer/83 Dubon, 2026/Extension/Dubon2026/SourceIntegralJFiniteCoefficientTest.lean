import Dubon2026.SourceIntegralPrimeTwoDegreeBounds

/-! The existing leading-coefficient identity gives a finite equality test for
integral polynomials evaluated at the actual j series. This is the precise test
used to identify the prime-two integral minimal polynomial from the computed
coefficients, required for the cyclic-quotient root interpretation, DUB-17/18. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial
noncomputable section

theorem eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero (P : Polynomial ℤ) (n : ℕ)
    (hP : P.natDegree ≤ n)
    (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) : P = 0 := by
  by_contra hne
  have hlc := coeff_evalAtJ_leading P
  rw [h _ (by omega) (by omega)] at hlc
  exact (leadingCoeff_ne_zero.mpr hne) (Int.cast_eq_zero.mp hlc.symm)

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

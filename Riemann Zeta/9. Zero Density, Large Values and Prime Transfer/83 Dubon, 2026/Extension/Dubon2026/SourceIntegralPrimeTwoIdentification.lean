import Dubon2026.SourceIntegralPrimeTwoCoefficient0
import Dubon2026.SourceIntegralPrimeTwoCoefficient1
import Dubon2026.SourceIntegralPrimeTwoCoefficient2

/-! The explicit classical prime-two cubic is the actual integral minimal
polynomial of the original j(2 tau) over the integral j-coordinate. The proof
assembles exact coefficient equalities and the previously proved monic degree.
This closes the polynomial identification input to the actual degree-two
cyclic-quotient product, required for the DUB-17 / DUB-18 inertia census. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial PhiTwoCalc
open Dubon2026.SourcePrimeTwoPolynomial

theorem modularPolynomial_two_eq_phiTwo : modularPolynomial 2 = phiTwo := by
  obtain ⟨h₀, h₁, h₂, h₃, hge⟩ := phiTwo_coeff
  apply Polynomial.ext
  intro k
  rcases lt_or_ge k 4 with hk | hk
  · interval_cases k
    · exact modularPolynomial_two_coeff_0_eq.trans h₀.symm
    · exact modularPolynomial_two_coeff_1_eq.trans h₁.symm
    · exact modularPolynomial_two_coeff_2_eq.trans h₂.symm
    · rw [h₃, ← show (modularPolynomial 2).natDegree = 3 from
        modularPolynomial_prime_natDegree 2, coeff_natDegree]
      exact (modularPolynomial_monic 2).leadingCoeff
  · rw [hge k hk, coeff_eq_zero_of_natDegree_lt (by
      rw [modularPolynomial_prime_natDegree]
      omega)]

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

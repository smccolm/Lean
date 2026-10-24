import Dubon2026.SourceExactIntegralModularPolynomial
import Dubon2026.SourceLevelPsiPrimeStep

/-! Base level and strict composition-degree bound for the actual cyclic
quotient induction. Reuse the original integral minimal polynomial and
proved Dedekind psi prime-step formulas. These discharge the arithmetic
premises of the finite-fiber counting argument on the DUB-17/18 chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial IntermediateField SourceLevelProjective
noncomputable section

/-- The exact original level-one integral relation is Y minus X. -/
theorem modularPolynomial_one : modularPolynomial 1 = X - C X := by
  apply Polynomial.map_injective evaluate evaluate_injective
  rw [modularPolynomial_map_coordinate, qExpand_one_apply]
  have hm : minpoly J jq = X - C (AdjoinSimple.gen ℚ jq) :=
    minpoly.eq_X_sub_C (LaurentSeries ℚ) (AdjoinSimple.gen ℚ jq)
  rw [hm]
  simp [evaluate]

/-- Its actual fiber has exactly the original coordinate as root. -/
theorem modularPolynomial_one_fiber {R : Type*} [CommRing R] (j : R) :
    relationAtSeed (modularPolynomial 1) j = X - C j := by
  simp [modularPolynomial_one, relationAtSeed]

/-- The prime composition product has strictly less than twice the required all-level degree. -/
theorem prime_composition_degree_lt {p M : ℕ} (hp : p.Prime) (hM : M ≠ 0) :
    (p + 1) * dedekindPsi M < 2 * dedekindPsi (p * M) := by
  have hpos := dedekindPsi_pos hM
  have hp2 := hp.two_le
  by_cases hd : p ∣ M
  · rw [Nat.mul_comm p M, dedekindPsi_mul_prime_dvd hM hp hd]
    nlinarith
  · rw [Nat.mul_comm p M, dedekindPsi_mul_prime_not_dvd hp hd]
    nlinarith

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

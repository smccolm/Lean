import Dubon2026.SourceIntegralJCoordinate
import Dubon2026.SourceOriginalAllLevelDegree
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! The literal j_N minimal polynomial over the integral j-coordinate
has degree psi(N). Its existence is derived from the existing integral
monic relation; native integrally-closed fraction-field descent and the
proved exact original field degree give its minimal degree. This is the
polynomial input to the finite exceptional-fiber orbit census, DUB-17/18. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField
variable (N : ℕ) [NeZero N]

theorem level_integral_over_int_polynomial : IsIntegral ℤ[X] (qExpand ℚ N jq) := by
  obtain ⟨P, hPm, hP0⟩ := exists_monic_relation N
  exact ⟨P, hPm, hP0⟩

/-- The actual integral minimal polynomial, with the original j-coordinate algebra. -/
def modularPolynomial : Polynomial (Polynomial ℤ) := minpoly ℤ[X] (qExpand ℚ N jq)

theorem modularPolynomial_monic : (modularPolynomial N).Monic :=
  minpoly.monic (level_integral_over_int_polynomial N)

theorem modularPolynomial_eval :
    (modularPolynomial N).eval₂ evalAtJ (qExpand ℚ N jq) = 0 :=
  minpoly.aeval ℤ[X] (qExpand ℚ N jq)

theorem modularPolynomial_map_coordinate :
    (modularPolynomial N).map evaluate = minpoly J (qExpand ℚ N jq) := by
  haveI := isFractionRing_coordinate
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' J
    (level_integral_over_int_polynomial N)).symm

theorem modularPolynomial_natDegree :
    (modularPolynomial N).natDegree = SourceLevelProjective.dedekindPsi N := by
  calc
    _ = ((modularPolynomial N).map evaluate).natDegree :=
      ((modularPolynomial_monic N).natDegree_map _).symm
    _ = (minpoly J (qExpand ℚ N jq)).natDegree := by rw [modularPolynomial_map_coordinate]
    _ = _ := (original_minpoly_degree_eq_full_relfinrank_of_generation N
      (original_full_eq_pair N)).trans (original_full_rational_relfinrank_eq_psi N)

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate

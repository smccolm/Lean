import Dubon2026.SourceModularCoefficientPolynomialIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership. Actual rational-coordinate
membership implies an actual polynomial identity because the substituted
j is integral and the transcendental polynomial coordinate is integrally
closed. This removes the denominator step from the remaining characteristic-p
obstruction, reusing the proved characteristic-zero descent argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem coefficient_j_polynomial_of_mem_rational (N : ℕ) [NeZero N]
    (K : Type*) [Field K]
    (hmem : qExpand K N (jqModC K) ∈
      IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    ∃ Q : K[X], Polynomial.aeval (jqModC K) Q = qExpand K N (jqModC K) := by
  let A := Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))
  let B := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))
  letI : UniqueFactorizationMonoid A := (transcendental_jqModC K).uniqueFactorizationMonoid_adjoin
  let x : B := ⟨qExpand K N (jqModC K), hmem⟩
  have hi : IsIntegral A x :=
    (isIntegral_algebraMap_iff (algebraMap B (LaurentSeries K)).injective).mp
      (coefficient_j_integral_polynomial_algebra N K)
  obtain ⟨P, hPm, hP0⟩ := hi
  obtain ⟨a, ha, _⟩ := exists_integer_of_is_root_of_monic hPm hP0
  have hx : qExpand K N (jqModC K) = (a : LaurentSeries K) := by
    have h := congrArg (fun t : B => (t : LaurentSeries K)) ha
    exact h.trans (IntermediateField.algebraAdjoinAdjoin.coe_algebraMap K
      ({jqModC K} : Set (LaurentSeries K)) a)
  have hm : qExpand K N (jqModC K) ∈ A := by rw [hx]; exact a.property
  change qExpand K N (jqModC K) ∈ Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)) at hm
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  exact (AlgHom.mem_range _).mp hm

end
end Dubon2026.SourceFunctionField

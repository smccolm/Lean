import Dubon2026.SourceCurveFiniteSupport
import Dubon2026.SourceOriginalUniformizerFinite

/-! DUB-17/18 -> regular differential dimension -> principal divisors.
The actual original field now has finite place support for every function's
normalized order. This discharges the finite-support part of the original
principal-divisor condition. SourceOriginalPrincipalDivisors also proves
degree zero and assembles the original curve interface.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem finite_original_places_positive
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (f : modularFunctionFieldOver N L) :
    {v : Place L (modularFunctionFieldOver N L) | 0 < v.ord f}.Finite := by
  classical
  by_cases ht : Transcendental L f
  · haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    letI : Algebra L (modularFunctionFieldOver N L) := inferInstance
    haveI : FiniteDimensional (IntermediateField.adjoin L {f}) (modularFunctionFieldOver N L) :=
      finiteDimensional_original_over_transcendental N L ht
    exact SourceCurve.finite_places_positive_of_finite_coordinate f ht
  · have ha : IsAlgebraic L f := not_not.mp ht
    have he : {v : Place L (modularFunctionFieldOver N L) | 0 < v.ord f} = ∅ := by
      ext v
      simp [v.ord_eq_zero_of_isAlgebraic ha]
    rw [he]
    exact Set.finite_empty

/-- Every function in the actual original field has only finitely many nonzero place orders. -/
theorem finite_original_divisor_support
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (f : modularFunctionFieldOver N L) :
    {v : Place L (modularFunctionFieldOver N L) | v.ord f ≠ 0}.Finite := by
  refine ((finite_original_places_positive N L f).union
    (finite_original_places_positive N L f⁻¹)).subset ?_
  intro v hv
  change 0 < v.ord f ∨ 0 < v.ord f⁻¹
  rw [v.ord_inv]
  change v.ord f ≠ 0 at hv
  omega

end
end Dubon2026.SourceFunctionField

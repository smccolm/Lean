import Dubon2026.SourceCurvePrincipalDegree
import Dubon2026.SourceCurveDivisors
import Dubon2026.SourceOriginalDivisorSupport
import Dubon2026.SourceOriginalResidueFinite
import Dubon2026.SourceOriginalDifferentialRank

/-! DUB-17/18 -> cusp-form dimension lower bound -> actual regular
differential dimension. The original field's principal divisors, finite
residues and one-dimensional differential space are proved and assembled.
Canonical divisors, Riemann--Roch, the geometric genus formula and analytic
cusp-form realization remain subsequent obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem sum_original_orders_eq_zero (f : modularFunctionFieldOver N L) :
    (∑ᶠ v : Place L (modularFunctionFieldOver N L),
      v.ord f * (Module.finrank L v.ResidueField : ℤ)) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact sum_orders_eq_zero_of_finite_coordinates
    (fun _ ht => finiteDimensional_original_over_transcendental N L ht)
    f (finite_original_divisor_support N L f)

/-- The actual finite normalized-order divisor of an original-field function. -/
def originalPrincipalDivisor (f : modularFunctionFieldOver N L) :
    Divisor L (modularFunctionFieldOver N L) :=
  Finsupp.ofSupportFinite (fun v => v.ord f) (finite_original_divisor_support N L f)

theorem originalPrincipalDivisor_apply (f : modularFunctionFieldOver N L)
    (v : Place L (modularFunctionFieldOver N L)) : originalPrincipalDivisor N L f v = v.ord f :=
  rfl

theorem degree_originalPrincipalDivisor (f : modularFunctionFieldOver N L) :
    Divisor.degree (originalPrincipalDivisor N L f) = 0 := by
  rw [Divisor.degree_eq_finsum]
  exact sum_original_orders_eq_zero N L f

/-- Principal-divisor existence and degree zero hold for the actual original field. -/
theorem hasPrincipalDivisors_original : HasPrincipalDivisors L (modularFunctionFieldOver N L) := by
  refine ⟨fun f _ => ⟨originalPrincipalDivisor N L f, ?_, degree_originalPrincipalDivisor N L f⟩⟩
  exact originalPrincipalDivisor_apply N L f

/-- All source curve inputs are derived for the actual original field over closed constants. -/
theorem isCurveOver_original [IsAlgClosed L] : IsCurveOver L (modularFunctionFieldOver N L) where
  toHasPrincipalDivisors := hasPrincipalDivisors_original N L
  finiteResidue := finite_original_place_residue N L
  kaehler_free_rank_one := ⟨inferInstance, finrank_original_differentials N L⟩

end
end Dubon2026.SourceFunctionField

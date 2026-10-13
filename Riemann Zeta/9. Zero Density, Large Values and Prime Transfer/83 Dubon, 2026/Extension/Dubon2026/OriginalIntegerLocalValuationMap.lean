import Dubon2026.CanonicalLocalizedIntegerMaps
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.NumberTheory.LocalField.Basic

/-! # Original number-field integers in the actual local valuation ring

This constructs the coefficient map needed to reuse unramified base change
on the actual local image of an arithmetic finite stage. It serves local H2
vanishing and finite support before DUB-17 global reciprocity and Selmer duality.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

variable (K E : Type) [Field K] [Field E] [Algebra K E] [ValuativeRel E]

/-- Every original algebraic integer has integral image under the original
field embedding into the valued local field. -/
theorem originalIntegerMap_mem_valuationInteger (x : 𝓞 K) :
    algebraMap K E (x : K) ∈ (ValuativeRel.valuation E).integer := by
  have hx : IsIntegral ℤ (algebraMap K E (x : K)) :=
    x.property.map (IsScalarTower.toAlgHom ℤ K E)
  exact (Valuation.integer.integers (ValuativeRel.valuation E)).mem_of_integral hx.tower_top

/-- The literal original field map restricted to the original integer ring. -/
def originalIntegerToValuationIntegerMap : 𝓞 K →+* 𝒪[E] :=
  ((algebraMap K E).comp (algebraMap (𝓞 K) K)).codRestrict _
    (originalIntegerMap_mem_valuationInteger K E)

/-- The constructed integer map has precisely the original field value. -/
theorem originalIntegerToValuationIntegerMap_coe (x : 𝓞 K) :
    (originalIntegerToValuationIntegerMap K E x : E) = algebraMap K E (x : K) := by
  rfl

end
end Dubon2026

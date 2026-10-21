import Dubon2026.SourceCurveLocalFinite
import Dubon2026.SourceOriginalUniformizerFinite

/-! DUB-17/18 -> canonical divisors -> local integral differentials.
The proved finite extension over every actual uniformizer gives an integral
chart at that place. Essential finite type and finite local differentials
are consequences for the literal original valuation ring.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

theorem essFiniteType_original_place
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (v : Place L (modularFunctionFieldOver N L)) :
    Algebra.EssFiniteType L v.toValuationSubring := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : FiniteDimensional (IntermediateField.adjoin L {v.uniformizer})
      (modularFunctionFieldOver N L) := finiteDimensional_original_over_uniformizer N L v
  apply essFiniteType_place_of_finite_coordinate v.uniformizer
    (v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)) v
  exact v.mem_of_ord_nonneg (by rw [v.ord_uniformizer]; omega)

theorem finite_original_place_differentials
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (v : Place L (modularFunctionFieldOver N L)) :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] := by
  haveI := essFiniteType_original_place N L v
  exact KaehlerDifferential.finite L v.toValuationSubring

end
end Dubon2026.SourceFunctionField

import Dubon2026.SourceCurveTranscendence
import Dubon2026.SourceCurveCoordinateExchange
import Dubon2026.SourceOriginalEssentialFiniteType
import Dubon2026.SourceOriginalLocalDifferentials

/-! DUB-17/18 -> analytic realization of regular differentials -> regularity
of local derivatives. Each actual uniformizer is now a separating finite
coordinate of the original modular function field. This discharges the
finite-extension premise needed for the local unramified-ring argument.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem finiteDimensional_original_over_transcendental
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    {t : modularFunctionFieldOver N L} (ht : Transcendental L t) :
    FiniteDimensional (IntermediateField.adjoin L {t}) (modularFunctionFieldOver N L) := by
  let F := modularFunctionFieldOver N L
  letI : Algebra L F := inferInstance
  let E := IntermediateField.adjoin L ({t} : Set F)
  let J := IntermediateField.adjoin L ({jOver N L} : Set F)
  letI : Algebra L E := inferInstance
  letI : Algebra L J := inferInstance
  haveI : FiniteDimensional J F :=
    finiteDimensional_original N L
  haveI : Algebra.IsAlgebraic J F := Algebra.IsAlgebraic.of_finite J F
  haveI : Algebra.IsAlgebraic E F :=
    SourceCurve.isAlgebraic_adjoin_of_transcendental (jOver N L) ht
  haveI : Algebra.EssFiniteType L F := essFiniteType_original N L
  haveI : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp L E F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- The actual field is finite over the rational coordinate of every genuine place uniformizer. -/
theorem finiteDimensional_original_over_uniformizer
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (v : Place L (modularFunctionFieldOver N L)) :
    FiniteDimensional (IntermediateField.adjoin L {v.uniformizer})
      (modularFunctionFieldOver N L) :=
  finiteDimensional_original_over_transcendental N L
    (v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero))

end
end Dubon2026.SourceFunctionField

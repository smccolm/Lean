import Dubon2026.SourceCurveResidueAlgebraic
import Dubon2026.SourceOriginalUniformizerFinite
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original regular differential dimension/local regularity.
For algebraically closed constant fields, every actual place has residue
field equal to the constants. Its finiteness is derived from the original
finite-coordinate theorem, without an IsCurveOver or finite-residue premise.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem original_place_residue_isAlgebraic
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
    (v : Place L (modularFunctionFieldOver N L)) : Algebra.IsAlgebraic L v.ResidueField :=
  ⟨v.isAlgebraic_residue_of_finite_coordinates
    (fun _ ht => finiteDimensional_original_over_transcendental N L ht)⟩

theorem original_place_residue_algebraMap_bijective
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (v : Place L (modularFunctionFieldOver N L)) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  haveI : Algebra.IsAlgebraic L v.ResidueField := original_place_residue_isAlgebraic N L v
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Every actual place of the original field has finite residue over algebraically closed constants. -/
theorem finite_original_place_residue
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (v : Place L (modularFunctionFieldOver N L)) : Module.Finite L v.ResidueField :=
  Module.Finite.of_surjective (Algebra.linearMap L v.ResidueField)
    (original_place_residue_algebraMap_bijective N L v).surjective

end
end Dubon2026.SourceFunctionField

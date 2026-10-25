import Dubon2026.SourceCurveSeparableDifferentialBaseChange
import Dubon2026.SourceCurveFiniteCoordinateGeometry
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceOriginalDifferentialRank

/-! DUB-17/18 -> Weil nondegeneracy -> geometry of auxiliary covers.
The native finite-coordinate geometry applies to actual finite extensions of
our original function field. No curve structure or residue-rationality
hypothesis is supplied by the caller. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]
local notation "F" => modularFunctionFieldOver N L
variable (E : Type*) [Field E] [Algebra (modularFunctionFieldOver N L) E] [Algebra L E]
variable [IsScalarTower L (modularFunctionFieldOver N L) E]
variable [FiniteDimensional (modularFunctionFieldOver N L) E]

theorem original_extension_finite_coordinate :
    FiniteDimensional L⟮algebraMap F E (jOver N L)⟯ E := by
  letI : FiniteDimensional L⟮jOver N L⟯ F := finiteDimensional_original N L
  apply Module.finite_of_finrank_pos
  rw [finrank_adjoin_algebraMap_mul]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

include N in
theorem original_extension_curve [IsAlgClosed L] : IsCurveOver L E := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap L F).injective
  letI := original_extension_finite_coordinate N L E
  have ht : Transcendental L (algebraMap F E (jOver N L)) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr (transcendental_jOver N L)
  exact isCurveOver_finite_coordinate _ ht
    (D_algebraMap_ne_zero_of_separable (D_jOver_ne_zero N L))

include N in
theorem original_extension_residue_bijective [IsAlgClosed L] (w : Place L E) :
    Function.Bijective (algebraMap L w.ResidueField) := by
  letI := original_extension_finite_coordinate N L E
  exact place_residue_bijective_of_finite_coordinate (algebraMap F E (jOver N L)) w

end
end Dubon2026.SourceFunctionField

import Dubon2026.SourceOriginalFiniteCoverGeometry
import Dubon2026.SourceOriginalWeilKummerCover

/-! DUB-17/18 -> Weil nondegeneracy -> the actual Kummer cover.
The literal polynomial splitting field satisfies the finite-coordinate,
curve and closed-residue conditions used by the detecting-class argument.
Picard divisibility and detection itself remain separate obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField Polynomial
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
local notation "F" => modularFunctionFieldOver N L
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

omit [IsAlgClosed L] in
theorem originalWeilKummerCover_finite_coordinate :
    Transcendental L (algebraMap F E (jOver N L)) ∧
      FiniteDimensional L⟮algebraMap F E (jOver N L)⟯ E :=
  ⟨(transcendental_algebraMap_iff (algebraMap F E).injective).mpr (transcendental_jOver N L),
    original_extension_finite_coordinate N L E⟩

theorem originalWeilKummerCover_curve : IsCurveOver L E :=
  original_extension_curve N L E

theorem originalWeilKummerCover_residue_bijective (w : Place L E) :
    Function.Bijective (algebraMap L w.ResidueField) :=
  original_extension_residue_bijective N L E w

end
end Dubon2026.SourceFunctionField

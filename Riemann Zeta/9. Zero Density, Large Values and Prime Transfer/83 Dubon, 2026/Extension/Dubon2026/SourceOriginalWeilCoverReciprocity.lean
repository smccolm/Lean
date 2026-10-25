import Dubon2026.SourceCurveFiniteCoordinateReciprocity
import Dubon2026.SourceOriginalWeilCoverNorm

/-! DUB-17/18 -> actual Weil nondegeneracy -> auxiliary Kummer cover.
The literal splitting field has proved finite-coordinate geometry, closed
residues and principal degree zero. They discharge all inputs of the norm
transfer and give reciprocity for actual nonzero functions and order divisors.
Picard division on this cover remains a separate mathematical obligation. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial IntermediateField
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "F" => modularFunctionFieldOver N L
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

theorem originalWeilKummerCover_reciprocity (g h : E) (hg : g ≠ 0) (hh : h ≠ 0)
    (Dg Dh : Divisor L E) (hDg : ∀ v, Dg v = v.ord g) (hDh : ∀ v, Dh v = v.ord h)
    (hdisj : ∀ v : Place L E, v.ord g ≠ 0 → v.ord h = 0) :
    originalWeilKummerDivisorEval N L n f g Dh =
      originalWeilKummerDivisorEval N L n f h Dg := by
  let t := algebraMap F E (jOver N L)
  haveI : FiniteDimensional L⟮t⟯ E := (originalWeilKummerCover_finite_coordinate N L n f).2
  haveI := originalWeilKummerCover_curve N L n f
  exact finite_coordinate_weil_reciprocity t
    (originalWeilKummerCover_residue_bijective N L n f) g h hg hh Dg Dh hDg hDh hdisj

end
end Dubon2026.SourceFunctionField

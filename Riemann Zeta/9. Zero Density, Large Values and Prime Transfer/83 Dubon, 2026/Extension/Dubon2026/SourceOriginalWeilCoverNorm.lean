import Dubon2026.SourceCurveRationalDivisorNorm
import Dubon2026.SourceOriginalWeilCoverEvaluation
import Dubon2026.SourceOriginalNormEvaluation

/-! DUB-17/18 -> the Kummer detecting class -> literal norm adjunction.
Apply the native finite norm and restriction formulas to the actual splitting
field and the existing original divisor evaluation. Geometry is discharged
by scope 481; only the stated disjoint-support regularity is required. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "F" => modularFunctionFieldOver N L
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

theorem originalWeilKummerDivisorEval_finitePullback (D : Divisor L F) (g : E)
    (hord : ∀ v ∈ D.support, ∀ w : Place L E, w.restrict F = v → 0 ≤ w.ord g) :
    originalWeilKummerDivisorEval N L n f g (Divisor.finitePullback E D) =
      originalDivisorEval N L (Algebra.norm F g) D :=
  rationalDivisorEval_finitePullback (original_place_residue_algebraMap_bijective N L)
    (originalWeilKummerCover_residue_bijective N L n f) D g hord

theorem originalDivisorEval_kummer_geometricPushforward (D : Divisor L E) (g : F)
    (hg : g ≠ 0) (hord : ∀ w ∈ D.support, w.ord (algebraMap F E g) = 0) :
    originalDivisorEval N L g (Divisor.geometricPushforward F D) =
      originalWeilKummerDivisorEval N L n f (algebraMap F E g) D :=
  rationalDivisorEval_geometricPushforward (original_place_residue_algebraMap_bijective N L)
    (originalWeilKummerCover_residue_bijective N L n f) D g hg hord

end
end Dubon2026.SourceFunctionField

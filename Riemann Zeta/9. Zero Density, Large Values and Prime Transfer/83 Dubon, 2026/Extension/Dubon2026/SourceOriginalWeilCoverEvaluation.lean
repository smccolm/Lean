import Dubon2026.SourceCurveRationalDivisorEvaluation
import Dubon2026.SourceOriginalWeilKummerGeometry
import Dubon2026.SourceOriginalWeilEvaluation

/-! DUB-17/18 -> the Kummer detecting class -> actual cover evaluations.
The cover residue hypotheses are discharged by its proved curve geometry.
The original-side evaluation is the existing one, with a definitional
comparison to the same general finite product. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalDivisorEval_eq_rationalDivisorEval
    (g : modularFunctionFieldOver N L) (D : Divisor L (modularFunctionFieldOver N L)) :
    originalDivisorEval N L g D =
      rationalDivisorEval (original_place_residue_algebraMap_bijective N L) g D := rfl

variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

/-- Actual divisor evaluation on the literal auxiliary Kummer splitting field. -/
def originalWeilKummerDivisorEval (g : E) (D : Divisor L E) : L :=
  rationalDivisorEval (originalWeilKummerCover_residue_bijective N L n f) g D

theorem originalWeilKummerDivisorEval_single (g : E) (v : Place L E) (m : ℤ) :
    originalWeilKummerDivisorEval N L n f g (Finsupp.single v m) =
      v.rationalEval (originalWeilKummerCover_residue_bijective N L n f v) g ^ m :=
  rationalDivisorEval_single _ g v m

theorem originalWeilKummerDivisorEval_ne_zero (g : E) (hg : g ≠ 0) (D : Divisor L E)
    (hD : ∀ v ∈ D.support, v.ord g = 0) : originalWeilKummerDivisorEval N L n f g D ≠ 0 :=
  rationalDivisorEval_ne_zero _ g hg D hD

theorem originalWeilKummerDivisorEval_mul (g h : E) (D : Divisor L E)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring)
    (hh : ∀ v ∈ D.support, h ∈ v.toValuationSubring) :
    originalWeilKummerDivisorEval N L n f (g * h) D =
      originalWeilKummerDivisorEval N L n f g D * originalWeilKummerDivisorEval N L n f h D :=
  rationalDivisorEval_mul _ g h D hg hh

theorem originalWeilKummerDivisorEval_add (g : E) (A B : Divisor L E)
    (h : ∀ v, v ∈ A.support ∨ v ∈ B.support →
      v.rationalEval (originalWeilKummerCover_residue_bijective N L n f v) g ≠ 0) :
    originalWeilKummerDivisorEval N L n f g (A + B) =
      originalWeilKummerDivisorEval N L n f g A * originalWeilKummerDivisorEval N L n f g B :=
  rationalDivisorEval_add _ g A B h

theorem originalWeilKummerDivisorEval_pow (g : E) (D : Divisor L E)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) (m : ℕ) :
    originalWeilKummerDivisorEval N L n f (g ^ m) D =
      originalWeilKummerDivisorEval N L n f g D ^ m :=
  rationalDivisorEval_pow _ g D hg m

theorem originalWeilKummerDivisorEval_nsmul (g : E) (D : Divisor L E) (m : ℕ) :
    originalWeilKummerDivisorEval N L n f g (m • D) =
      originalWeilKummerDivisorEval N L n f g D ^ m :=
  rationalDivisorEval_nsmul _ g D m

end
end Dubon2026.SourceFunctionField

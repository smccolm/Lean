import Dubon2026.SourceInducedCoefficientMap
import Dubon2026.SourceRegularDifferentialEvaluation

/-! Coefficient change for the actual infinitesimal source action.
Both sides evaluate the same original function at the same infinitesimal
matrix. This will derive Lie stability of the integral generic-fibre image.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}

/-- The original infinitesimal point at the extended generic matrix is the actual extended infinitesimal generic point. -/
theorem sourceCoefficient_infinitesimalPoint (X : Matrix (Fin n) (Fin n) R) :
    sourceInfinitesimalPointAt X (generalLinearRegularGeneric B n) =
      sourceRegularInfinitesimalPoint (X.map (algebraMap R B)) := by
  unfold sourceInfinitesimalPointAt sourceRegularInfinitesimalPoint
  congr 1

/-- The original source differential commutes with actual coefficient change. -/
theorem sourceRegularCoefficientMap_differential
    (X : Matrix (Fin n) (Fin n) R) (p : GeneralLinearRegularFunctions R n) :
    sourceRegularCoefficientMap R B n (sourceRegularDifferential X p) =
      sourceRegularDifferential (X.map (algebraMap R B))
        (sourceRegularCoefficientMap R B n p) := by
  change generalLinearRegularEval (R := R) (generalLinearRegularGeneric B n)
      (sourceRegularDifferential X p) =
    (generalLinearRegularEval (R := B) (A := DualNumber (GeneralLinearRegularFunctions B n))
      (sourceRegularInfinitesimalPoint (X.map (algebraMap R B)))
        (sourceRegularCoefficientMap R B n p)).snd
  rw [sourceRegularDifferential_eval (R := R) (A := GeneralLinearRegularFunctions B n)]
  have he := sourceRegularCoefficientMap_eval R B n
    (A := DualNumber (GeneralLinearRegularFunctions B n))
    (sourceRegularInfinitesimalPoint (X.map (algebraMap R B))) p
  rw [he, sourceCoefficient_infinitesimalPoint]

end
end Dubon2026

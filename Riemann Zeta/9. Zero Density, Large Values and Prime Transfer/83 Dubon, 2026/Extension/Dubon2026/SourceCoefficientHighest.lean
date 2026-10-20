import Dubon2026.SourceInducedCoefficientMap
import Dubon2026.IntegralDominantHighestLine

/-! The same normalized highest vector in the integral and field coefficients.
All-algebra evaluation preserves the original highest character, and the
proved unique normalization identifies the image with the original vector
over the new coefficient ring. No minor expansion is reproved.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [IsDomain B]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

/-- Original coefficient change preserves the actual normalized highest vector. -/
theorem sourceInducedCoefficientMap_highest :
    sourceInducedCoefficientMap R B (m + 1) weight
      (integralDominantHighestVector R weight hw) =
        integralDominantHighestVector B weight hw := by
  apply integralDominantHighestLine_normalized_unique B weight hw
  · intro A _ _ g b
    letI : Algebra R A := Algebra.compHom A (algebraMap R B)
    letI : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' rfl
    change generalLinearRegularEval (R := B) (g * b.val)
        (sourceRegularCoefficientMap R B (m + 1) (integralDominantHighestRegular R weight)) =
      _ * generalLinearRegularEval (R := B) g
        (sourceRegularCoefficientMap R B (m + 1) (integralDominantHighestRegular R weight))
    rw [sourceRegularCoefficientMap_eval, sourceRegularCoefficientMap_eval]
    exact integralDominantHighestRegular_right_borel R weight hw g b
  · change generalLinearRegularEval (R := B) (integralWeightLongest B (m + 1))
      (sourceRegularCoefficientMap R B (m + 1) (integralDominantHighestRegular R weight)) = 1
    rw [sourceRegularCoefficientMap_eval]
    have he := AlgHom.congr_fun (generalLinearRegularEval_natural
      (Algebra.ofId R B) (integralWeightLongest R (m + 1)))
      (integralDominantHighestRegular R weight)
    rw [integralWeightLongest_map] at he
    rw [← he, AlgHom.comp_apply, integralDominantHighestRegular_longest, map_one]

end
end Dubon2026

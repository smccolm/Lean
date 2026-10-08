import Dubon2026.RealSL2Characters
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # The actual Iwasawa Haar measure is invariant on both sides -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

instance realSpecialLinear_locallyCompactSpace : LocallyCompactSpace SL(2, ℝ) := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact (isClosedEmbedding_val (n := Fin 2) (R := ℝ)).locallyCompactSpace

instance realSpecialLinear_secondCountableTopology : SecondCountableTopology SL(2, ℝ) := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact (isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isEmbedding.secondCountableTopology

/-- The genuine real special-linear modular character is trivial, by actual elementary commutators. -/
theorem realSL2_modularCharacter_eq_one (g : SL(2, ℝ)) :
    Measure.modularCharacterFun g = 1 :=
  realSL2_commutative_character Measure.modularCharacter g

/-- The constructed original Iwasawa measure is genuinely right invariant as well as left invariant. -/
instance realGroupMeasure_isMulRightInvariant : realGroupMeasure.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul realGroupMeasure g,
      realSL2_modularCharacter_eq_one, one_smul]

/-- Every actual right real-group translation preserves the same original Haar measure. -/
theorem realGroupMeasure_right_invariant (g : SL(2, ℝ)) :
    MeasurePreserving (fun h : SL(2, ℝ) => h * g) realGroupMeasure realGroupMeasure :=
  measurePreserving_mul_right realGroupMeasure g

end
end Dubon2026

import Dubon2026.FiniteAdelicProjectiveCharacters
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Genuine unimodularity and both-sided Haar invariance of finite adelic PGL2 -/

namespace Dubon2026

noncomputable section
open MeasureTheory

/-- The original finite projective group's actual modular character is one by proved elementary matrix identities. -/
theorem finiteProjectiveGL2_modularCharacter_eq_one (g : RationalFiniteProjectiveGL2) :
    Measure.modularCharacterFun g = 1 :=
  finiteProjectiveGL2_nonnegative_character Measure.modularCharacter g

instance finiteProjectiveGL2MeasureIsMulRightInvariant : finiteProjectiveGL2Measure.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    letI : Measure.InnerRegular finiteProjectiveGL2Measure := by
      unfold finiteProjectiveGL2Measure
      infer_instance
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul finiteProjectiveGL2Measure g,
      finiteProjectiveGL2_modularCharacter_eq_one, one_smul]

/-- Every actual right translation preserves the same genuine normalized finite projective Haar measure. -/
theorem finiteProjectiveGL2Measure_right_invariant (g : RationalFiniteProjectiveGL2) :
    MeasurePreserving (fun h : RationalFiniteProjectiveGL2 => h * g)
      finiteProjectiveGL2Measure finiteProjectiveGL2Measure :=
  measurePreserving_mul_right finiteProjectiveGL2Measure g

end
end Dubon2026

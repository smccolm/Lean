import Dubon2026.OriginalClassesModOutsideH2Comparison
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # Original quotient H2 at every actual arithmetic finite stage

Proved absolute unramifiedness discharges all outside-unit hypotheses.
The literal full-class quotient therefore induces an isomorphism on H2
at every actual stage, including noncyclic extensions. This supplies the
finite coefficient comparison needed for DUB-17's class-formation route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The actual arithmetic union retains its original rational field inclusion. -/
local instance classGeneralH2UnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The actual finite stage retains its original rational field inclusion. -/
local instance classGeneralH2StageAlgebra : Algebra ℚ F := F.algebra'
/-- The actual finite arithmetic stage is a number field. -/
local instance classGeneralH2StageNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- The actual full-class H2 and arithmetic quotient H2 agree through the literal quotient map. -/
def rationalArithmeticClassesModOutsideStageH2Iso :
    groupCohomology (originalIdeleClassRep ℚ F) 2 ≅
      groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2 :=
  originalClassesModOutsideH2Iso ℚ F _ _
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

/-- Every original arithmetic quotient H2 class at any finite stage has a unique genuine full-class preimage. -/
theorem rationalArithmeticClassesModOutsideStage_H2_unique_full_class
    (x : groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) :
    ∃! y : groupCohomology (originalIdeleClassRep ℚ F) 2,
      (groupCohomology.functor ℤ Gal(F/ℚ) 2).map
        (originalIdeleClassesModOutsideRepHom ℚ F
          (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
          (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)) y = x :=
  originalClassesModOutside_H2_unique_full_class ℚ F _ _
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F) x

/-- The actual arithmetic stage quotient H2 is finite with order dividing its original field degree. -/
theorem rationalArithmeticClassesModOutsideStage_second_card_dvd :
    Finite (groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) ∧
      Nat.card (groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) ∣
        Module.finrank ℚ F :=
  originalClassesModOutside_finiteGalois_second_card_dvd ℚ F _ _
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

end
end Dubon2026

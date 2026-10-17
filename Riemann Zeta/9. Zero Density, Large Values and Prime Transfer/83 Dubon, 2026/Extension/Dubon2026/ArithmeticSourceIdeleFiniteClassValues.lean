import Dubon2026.ArithmeticSourceIdeleRelationMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceIdeleFiniteValuesUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The same source-to-full-class comparison retains the literal finite
source-idele representative, its original quotient and stage comparison. -/
theorem arithmeticSourceIdeleToFullClassColimit_of
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceFiniteStageRep ℚ Ω a ha F) :
    (arithmeticSourceIdeleToFullClassColimit Ω a ha).hom
      ((coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
        (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) F).hom x) =
    (coefficientRepresentationColimitOf (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F).hom
        ((arithmeticSourceClassStageComparison ℚ Ω a ha F).hom
          ((arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha F).hom x)) := by
  have hq : (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha).hom
      ((coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
        (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) F).hom x) =
      (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceClassStageRep ℚ Ω a ha)
        (arithmeticGlobalSPlaceClassStageTransition ℚ Ω a ha) F).hom
          ((arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha F).hom x) :=
    arithmeticSPlaceColimitQuotient_of ℚ Ω a ha F x
  exact (congrArg (arithmeticSourceClassColimitComparison ℚ Ω a ha).hom hq).trans
    (arithmeticSourceClassColimitComparison_of ℚ Ω a ha F _)

end
end Dubon2026

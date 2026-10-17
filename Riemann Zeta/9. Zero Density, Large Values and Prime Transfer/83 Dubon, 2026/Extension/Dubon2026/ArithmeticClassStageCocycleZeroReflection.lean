import Dubon2026.ArithmeticClassesModOutsideH2Inflation
import Dubon2026.ArithmeticClassStageCocycleTransition
import Dubon2026.ArithmeticOriginalStageClassImageZero

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original rational inclusion of the arithmetic union. -/
local instance classCocycleZeroReflectionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the original rational inclusions of the finite arithmetic fields. -/
local instance classCocycleZeroReflectionStageAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Retain the identical rational inclusion on the underlying intermediate field. -/
local instance classCocycleZeroReflectionIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : IntermediateField ℚ V) : Algebra ℚ E := E.algebra'


/-- The literal finite arithmetic cocycle transition reflects H2 zero,
with the original field inclusion and class coefficient map unchanged. -/
theorem rationalArithmeticClassStageTwoCocycleTransition_H2_eq_zero_iff
    (E F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F)
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep ℚ Ω a ha E)) :
    groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E F hEF c) = 0 ↔
      groupCohomology.H2π _ c = 0 := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower ℚ E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  let f := groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/ℚ) →* Gal(E/ℚ))
    (arithmeticClassesModOutsideFiniteTransition ℚ Ω a ha E F hEF) 2
  have hf : Function.Injective f := rationalArithmeticClassesModOutsideH2Inflation_injective Ω a ha E F hEF
  have hmap := groupCohomology.H2π_comp_map_apply
    (AlgEquiv.restrictNormalHom E : Gal(F/ℚ) →* Gal(E/ℚ))
    (arithmeticClassesModOutsideFiniteTransition ℚ Ω a ha E F hEF) c
  constructor
  · intro hz
    apply hf
    exact (hmap.trans hz).trans (map_zero f.hom).symm
  · intro hz
    exact hmap.symm.trans ((congrArg f hz).trans (map_zero f.hom))

/-- Vanishing at the actual common finite comparison field reflects all
the way back to the scalar stage's original class, including its realization
inside the arithmetic union. No normalized invariant is assumed here. -/
theorem arithmeticOriginalStageClassTwoCocycle_common_H2_eq_zero_iff
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hLM : originalUnramifiedStageInUnion a L ≤ M)
    (c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L)) :
    groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
      (originalUnramifiedStageInUnion a L) M hLM
      (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L c)) = 0 ↔
        groupCohomology.H2π _ c = 0 :=
  (rationalArithmeticClassStageTwoCocycleTransition_H2_eq_zero_iff Ω a ha
    (originalUnramifiedStageInUnion a L) M hLM
    (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L c)).trans
      (arithmeticOriginalStageClassTwoCocycleToImage_H2_eq_zero_iff Ω a ha L c)

end
end Dubon2026

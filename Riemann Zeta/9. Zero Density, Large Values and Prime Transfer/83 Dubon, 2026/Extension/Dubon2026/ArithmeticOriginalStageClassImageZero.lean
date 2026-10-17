import Dubon2026.ArithmeticOriginalStageClassCocycleImage
import Dubon2026.OriginalClassesModOutsideH2Inflation
import Dubon2026.ArithmeticOriginalStageSubgroupClassH2
import Dubon2026.ArithmeticClassesModOutsideH2Comparison

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance originalStageImageH2ZeroUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance originalStageImageH2ZeroFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance originalStageImageH2ZeroIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'



variable (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)

omit [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
/-- Realizing the original scalar-stage cocycle in its finite arithmetic
image reflects H2 zero through the proved original class inflation injection.
The original and image fields' outside-unramified conditions are derived. -/
theorem arithmeticOriginalStageClassTwoCocycleToImage_H2_eq_zero_iff
    (c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L)) :
    groupCohomology.H2π _ (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L c) = 0 ↔
      groupCohomology.H2π _ c = 0 := by
  let M := originalUnramifiedStageInUnion a L
  let e := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra L.val M := e.toAlgHom.toAlgebra
  letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
  letI : NumberField M := NumberField.of_module_finite ℚ M
  let f := groupCohomology.map (AlgEquiv.restrictNormalHom L.val : Gal(M/ℚ) →* Gal(L.val/ℚ))
    (arithmeticOriginalStageClassToImage Ω a ha L) 2
  have hf : Function.Injective f := originalClassesModOutsideH2Inflation_injective ℚ L.val M
    _ _ (originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha)
    (originalExceptionalIntegerSupport_galoisStable M ℚ a ha)
    (originalRationalExceptionalSupport_tower L.val M a ha)
    (arithmeticOriginalStage_outside_unramified Ω a ha L)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha M)
  have hmap := groupCohomology.H2π_comp_map_apply
    (AlgEquiv.restrictNormalHom L.val : Gal(M/ℚ) →* Gal(L.val/ℚ))
    (arithmeticOriginalStageClassToImage Ω a ha L) c
  constructor
  · intro hz
    apply hf
    exact (hmap.trans hz).trans (map_zero f.hom).symm
  · intro hz
    exact hmap.symm.trans ((congrArg f hz).trans (map_zero f.hom))

end
end Dubon2026

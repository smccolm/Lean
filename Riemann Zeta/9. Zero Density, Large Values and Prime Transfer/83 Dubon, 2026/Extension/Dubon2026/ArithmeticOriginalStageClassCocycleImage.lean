import Dubon2026.ArithmeticClassStageContinuousCocycle
import Dubon2026.ArithmeticOriginalStageClassColimit
import Dubon2026.OriginalScalarStageRestrictionContinuity

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance originalStageCocycleImageUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance originalStageCocycleImageFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance originalStageCocycleImageIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'


variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticOriginalStageClassCocycleImageLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- Realize the scalar stage's actual class two-cocycle in its literal
finite Galois image inside the arithmetic union. -/
def arithmeticOriginalStageClassTwoCocycleToImage
    (c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L)) :
    groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep ℚ Ω a ha
      (originalUnramifiedStageInUnion a L)) := by
  let M := originalUnramifiedStageInUnion a L
  let e := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra L.val M := e.toAlgHom.toAlgebra
  letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
  exact groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom L.val : Gal(M/ℚ) →* Gal(L.val/ℚ))
    (arithmeticOriginalStageClassToImage Ω a ha L) c

/-- The scalar-stage class cocycle enters the arithmetic continuous class
coefficient by its original restriction and class-colimit inclusion. -/
def arithmeticOriginalStageClassContinuousTwoCocycle
    (c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L)) :
    continuousRepresentationCocyclesTwo (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra L.val U :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val U :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  let π : Gal(U/ℚ) →* Gal(L.val/ℚ) := AlgEquiv.restrictNormalHom L.val
  let j := arithmeticOriginalStageClassToColimit Ω a ha L
  refine ⟨groupCohomology.mapCocycles₂ π j c, ?_⟩
  have hπ := originalScalarStageRestriction_continuous Ω a L
  exact (continuous_of_discreteTopology : Continuous (fun z : Gal(L.val/ℚ) × Gal(L.val/ℚ) =>
    j.hom (c z))).comp (hπ.prodMap hπ)

/-- Realizing the original scalar field inside the arithmetic union
preserves its exact continuous class cocycle, not only its algebraic image. -/
theorem arithmeticOriginalStageClassTwoCocycleToImage_continuous
    (c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L)) :
    arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha (originalUnramifiedStageInUnion a L)
      (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L c) =
        arithmeticOriginalStageClassContinuousTwoCocycle Ω a ha L c := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let M := originalUnramifiedStageInUnion a L
  let e := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra L.val M := e.toAlgHom.toAlgebra
  letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
  letI : Algebra L.val U :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val U :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  letI : IsScalarTower L.val M U := IsScalarTower.of_algebraMap_eq' rfl
  apply Subtype.ext
  apply Subtype.ext
  funext gh
  change (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) M).hom
      ((arithmeticOriginalStageClassToImage Ω a ha L).hom
        (c (AlgEquiv.restrictNormalHom L.val (AlgEquiv.restrictNormalHom M gh.1),
          AlgEquiv.restrictNormalHom L.val (AlgEquiv.restrictNormalHom M gh.2)))) = _
  rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L.val M gh.1,
    ← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L.val M gh.2]
  exact (arithmeticOriginalStageClassToColimit_apply Ω a ha L _).symm

end
end Dubon2026

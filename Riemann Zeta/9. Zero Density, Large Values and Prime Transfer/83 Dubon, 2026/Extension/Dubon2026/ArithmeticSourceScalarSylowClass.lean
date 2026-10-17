import Dubon2026.ArithmeticSourceScalarSylowCriterion
import Dubon2026.ArithmeticOriginalStageSubgroupClassH2

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceSylowClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceSylowClassFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceSylowClassHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual scalar-stage obstruction in full idele-class H2 over
the coefficient prime's Sylow fixed field. All maps are the original maps. -/
def arithmeticSourceScalarSylowClass
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) (S : Sylow p Gal(L.val/ℚ)) :
    groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1 →ₗ[ℤ]
    groupCohomology (originalIdeleClassRep
      (IntermediateField.fixedField (S : Subgroup Gal(L.val/ℚ))) L.val) 2 := by
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
  let e := arithmeticOriginalStageSubgroupClassH2Iso Ω a ha L (S : Subgroup Gal(L.val/ℚ))
  let ρ := groupCohomology.map (S : Subgroup Gal(L.val/ℚ)).subtype
    (𝟙 (Rep.res (S : Subgroup Gal(L.val/ℚ)).subtype C)) 2
  exact e.inv.hom.comp (ρ.hom.comp (originalRelationExtensionObstruction BL C ψ).hom)

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- Vanishing of the original scalar obstruction is equivalent to vanishing
of this actual full-class H2 element over the prime-power fixed-field stage. -/
theorem arithmeticSourceScalarObstruction_eq_zero_iff_sylowClass
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(L.val/ℚ))
    (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1) :
    let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
    let C := arithmeticOriginalStageClassRep Ω a ha L
    let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
    (originalRelationExtensionObstruction BL C ψ).hom y = 0 ↔
      arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S y = 0 := by
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
  let e := arithmeticOriginalStageSubgroupClassH2Iso Ω a ha L (S : Subgroup Gal(L.val/ℚ))
  let ρ := groupCohomology.map (S : Subgroup Gal(L.val/ℚ)).subtype
    (𝟙 (Rep.res (S : Subgroup Gal(L.val/ℚ)).subtype C)) 2
  have he : Function.Injective e.inv.hom := (ModuleCat.mono_iff_injective e.inv).mp inferInstance
  have hz (z) : e.inv.hom z = 0 ↔ z = 0 := he.eq_iff' (map_zero e.inv.hom)
  exact (arithmeticSourceScalarObstruction_eq_zero_iff_sylow Ω a ha P B c r F i L hFL p hB S y).trans
    (hz (ρ.hom ((originalRelationExtensionObstruction BL C ψ).hom y))).symm

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The same full-class representative is killed by the original coefficient
prime; this removes a separate primary-component assumption. -/
theorem arithmeticSourceScalarSylowClass_nsmul_zero
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) (S : Sylow p Gal(L.val/ℚ))
    (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1) :
    p • arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S y = 0 := by
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  have hBL (b : BL) : p • b = 0 := hB b
  let f := arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S
  have h := congrArg f (originalH1_nsmul_zero BL p hBL y)
  exact (map_nsmul f p y).symm.trans (h.trans (map_zero f))

end
end Dubon2026

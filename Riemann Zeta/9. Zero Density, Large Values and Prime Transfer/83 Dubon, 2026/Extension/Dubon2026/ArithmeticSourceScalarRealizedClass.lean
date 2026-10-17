import Dubon2026.ArithmeticSourceScalarSylowClass
import Dubon2026.OriginalScalarFixedClassRealization

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceRealizedClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceRealizedClassFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceRealizedClassHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual source obstruction, after Sylow restriction and full-class
comparison, transported through the original field embeddings into the
fixed arithmetic union. -/
def arithmeticSourceScalarRealizedClass
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) (S : Sylow p Gal(L.val/ℚ)) :
    groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1 →ₗ[ℤ]
      originalScalarFixedFieldRealizedClassH2 Ω a L (S : Subgroup Gal(L.val/ℚ)) :=
  (originalScalarFixedFieldClassRealization Ω a L (S : Subgroup Gal(L.val/ℚ))).comp
    (arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S)

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The literal class in the fixed arithmetic union detects precisely
the original scalar relation obstruction; no realization hypothesis is needed. -/
theorem arithmeticSourceScalarObstruction_eq_zero_iff_realizedClass
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
      arithmeticSourceScalarRealizedClass Ω a ha P B c r F i L hFL p S y = 0 := by
  let f := originalScalarFixedFieldClassRealization Ω a L (S : Subgroup Gal(L.val/ℚ))
  have hf : Function.Injective f := originalScalarFixedFieldClassRealization_injective Ω a L
    (S : Subgroup Gal(L.val/ℚ))
  have hz (z) : f z = 0 ↔ z = 0 := hf.eq_iff' (map_zero f)
  exact (arithmeticSourceScalarObstruction_eq_zero_iff_sylowClass
    Ω a ha P B c r F i L hFL p S hB y).trans
    (hz (arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S y)).symm

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The actual realized source class retains the original coefficient
prime annihilator. -/
theorem arithmeticSourceScalarRealizedClass_nsmul_zero
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) (S : Sylow p Gal(L.val/ℚ))
    (hB : ∀ b : B, p • b = 0)
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1) :
    p • arithmeticSourceScalarRealizedClass Ω a ha P B c r F i L hFL p S y = 0 := by
  let f := originalScalarFixedFieldClassRealization Ω a L (S : Subgroup Gal(L.val/ℚ))
  let z := arithmeticSourceScalarSylowClass Ω a ha P B c r F i L hFL p S y
  have h := congrArg f (arithmeticSourceScalarSylowClass_nsmul_zero
    Ω a ha P B c r F i L hFL p S hB y)
  exact (map_nsmul f p z).symm.trans (h.trans (map_zero f))

end
end Dubon2026

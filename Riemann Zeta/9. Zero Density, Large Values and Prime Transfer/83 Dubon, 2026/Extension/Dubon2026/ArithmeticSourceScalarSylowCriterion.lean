import Dubon2026.ArithmeticSourceScalarStageRelationMaps
import Dubon2026.OriginalRelationObstructionSylowDetection

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceSylowDetectionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceSylowDetectionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceSylowDetectionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The actual transported source-cocycle obstruction is detected on the
coefficient prime's Sylow subgroup. Its annihilator is derived from the
original coefficient, independently of the full scalar-stage degree. -/
theorem arithmeticSourceScalarObstruction_eq_zero_iff_sylow
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    (S : Sylow p Gal(L.val/ℚ))
    (y : groupCohomology (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL) 1) :
    let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
    let C := arithmeticOriginalStageClassRep Ω a ha L
    let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
    (originalRelationExtensionObstruction BL C ψ).hom y = 0 ↔
      (groupCohomology.map (S : Subgroup Gal(L.val/ℚ)).subtype
        (𝟙 (Rep.res (S : Subgroup Gal(L.val/ℚ)).subtype C)) 2).hom
          ((originalRelationExtensionObstruction BL C ψ).hom y) = 0 := by
  let BL := arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let ψ := arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL
  have hBL (b : BL) : p • b = 0 := hB b
  exact originalRelationExtensionObstruction_eq_zero_iff_sylow BL C p hBL S ψ y

end
end Dubon2026

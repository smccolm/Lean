import Dubon2026.ArithmeticSourceClassScalarStage
import Dubon2026.OriginalUnramifiedStageInUnion

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarUnionPlacementUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarUnionPlacementFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarUnionPlacementHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The original source cocycle constructs the same scalar-criterion stage,
whose literal realization inside the arithmetic union contains its descended
finite relation stage. The original scalar criterion is retained unchanged. -/
theorem arithmeticSourceClassHomCocycle_exists_scalar_stage_in_union
    [Finite B]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (hB : ∀ b : B, p • b = 0)
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
      ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : r.stage →ₐ[ℚ] F.val,
        (∀ x : r.stage, (i x : Ω) = (x.val : Ω)) ∧
        let BF := arithmeticOriginalStageRestrictedCoefficient Ω a r.stage F i
          (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)
        ∃ L : OriginalUnramifiedGaloisStage (Ω := Ω) a,
          ∃ hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField,
            r.stage ≤ originalUnramifiedStageInUnion a L ∧
            letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
            letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
            let T := originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
              (originalIntegerMap_ne_zero (L := L.val) a ha)
            let hT := originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha
            let C := originalIdeleClassesModOutsideRep ℚ L.val T hT
            let BL := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(L.val/ℚ) →* Gal(F.val/ℚ)) BF
            ∃ d : OriginalRelationPrimePairingData BL C p,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha r.stage F i
                (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) L hFL
                  (arithmeticSourceClassRelationStageHom Ω a ha P B c r)
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(L.val/ℚ) BL ⟶ C, originalRelationInclusion BL ≫ f = ψ := by
  obtain ⟨r, F, i, hi, L, hFL, hcriterion⟩ :=
    arithmeticSourceClassHomCocycle_exists_scalar_relation_stage Ω a ha P B p hp2 hpa hB c
  refine ⟨r, F, i, hi, L, hFL, ?_, hcriterion⟩
  exact (originalUnramifiedStageInUnion_contains_embedded a r.stage F i hi).trans
    (originalUnramifiedStageInUnion_mono a F L hFL)

end
end Dubon2026

import Dubon2026.ArithmeticSourceClassCocycleFiniteRelation
import Dubon2026.ArithmeticOriginalRelationScalarConsumer

/-! # Actual source-cocycle data at the constructed scalar relation stage

The original cocycle produces every field, morphism and comparison identity
in the returned data. The actual finite relation is then transported to the
constructed scalar criterion. Packaging the concrete witnesses keeps the
same dependency chain within default elaboration limits; no input certificate
is introduced. DUB-17's continuous/local cup identification remains open.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceScalarStageUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceScalarStageFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceScalarStageHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual original relation sequence restricted from its finite coefficient field. -/
abbrev arithmeticSourceRelationPresentation :=
  (originalRelationShortComplex B).map (Rep.resFunctor (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)))

/-- Actual witnesses constructed from the given source-class cocycle.
The fields retain every lift, relation and value identity; this data is
constructed below, never supplied as a premise of the arithmetic result. -/
structure ArithmeticSourceClassRelationData
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) where
  /-- The actual linear lift on the original free cover. -/
  lift : arithmeticRelationFreeClassHom Ω a ha P B
  /-- Its original equivariant relation-to-class morphism. -/
  relation : (arithmeticSourceRelationPresentation Ω a P B).X₁ ⟶
    arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  /-- The relation morphism is the literal restriction of the lift. -/
  relation_eq : relation.hom.toLinearMap =
    (show (arithmeticSourceRelationPresentation Ω a P B).X₂ →ₗ[ℤ]
      arithmeticClassesModOutsideColimitRep ℚ Ω a ha from lift).comp
        (arithmeticSourceRelationPresentation Ω a P B).f.hom.toLinearMap
  /-- The lift has exactly the original source-class cocycle as its coboundary. -/
  lift_coboundary : ∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g lift - lift =
    (originalInternalHomPrecomposition (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticSourceRelationPresentation Ω a P B).g).hom
        ((arithmeticSourceClassHomComparison ℚ Ω a ha
          (Rep.res (AlgEquiv.restrictNormalHom P :
            Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B)).hom (c.val g))
  /-- The actual finite Galois class stage. -/
  stage : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)
  /-- The actual coefficient field is contained in that stage. -/
  le_stage : P ≤ stage
  /-- The actual descended relation morphism. -/
  finiteRelation :
    letI : Algebra P stage := (IntermediateField.inclusion le_stage).toAlgebra
    letI : Module P stage := Algebra.toModule
    letI : SMul P stage := (IntermediateField.inclusion le_stage).toAlgebra.toSMul
    letI : IsScalarTower ℚ P stage := IsScalarTower.of_algHom (IntermediateField.inclusion le_stage)
    let τ : Gal(stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha stage
  /-- Descent preserves the literal relation restriction and colimit values. -/
  finiteRelation_values :
    letI : Algebra P stage := (IntermediateField.inclusion le_stage).toAlgebra
    letI : Module P stage := Algebra.toModule
    letI : SMul P stage := (IntermediateField.inclusion le_stage).toAlgebra.toSMul
    letI : IsScalarTower ℚ P stage := IsScalarTower.of_algHom (IntermediateField.inclusion le_stage)
    let τ : Gal(stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    ∀ r, (coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) stage).hom (finiteRelation.hom r) =
        relation.hom ((originalRelationGroupChange τ B).hom r)

omit [IsAlgClosure ℚ Ω] in
/-- The complete original source-cocycle relation data is constructed
from the proved free-cover coboundary and finite-lattice descent. -/
theorem arithmeticSourceClassRelationData_nonempty [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    Nonempty (ArithmeticSourceClassRelationData Ω a ha P B c) := by
  obtain ⟨v, φ, hφ, hv, N, hPN, hN⟩ :=
    arithmeticSourceClassHomCocycle_exists_finite_relation_representative Ω a ha P B c
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : Module P N := Algebra.toModule
  letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
  letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  obtain ⟨η, hη⟩ := hN
  exact ⟨⟨v, φ, hφ, hv, N, hPN, η, hη⟩⟩

/-- The actual coefficient at the constructed finite relation stage. -/
abbrev arithmeticSourceClassRelationStageCoefficient
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) : Rep.{0} ℤ Gal(r.stage/ℚ) := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := Algebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  exact Rep.res (AlgEquiv.restrictNormalHom P : Gal(r.stage/ℚ) →* Gal(P/ℚ)) B

/-- The actual finite relation morphism with its original coefficient action. -/
abbrev arithmeticSourceClassRelationStageHom
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :
    originalRelationModule (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r) ⟶
      arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage := r.finiteRelation

/-- The original source-class cocycle constructs its own relation data
and reaches the scalar vanishing/extension criterion on that same relation. -/
theorem arithmeticSourceClassHomCocycle_exists_scalar_relation_stage
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
  let r := Classical.choice (arithmeticSourceClassRelationData_nonempty Ω a ha P B c)
  refine ⟨r, ?_⟩
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  obtain ⟨F, i, hi, L, hFL, hL⟩ :=
    arithmeticClassRelation_exists_original_scalar_criterion Ω a ha r.stage p hp2 hpa BN hB
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  obtain ⟨d, hd⟩ := hL
  exact ⟨F, i, hi, L, hFL, d, hd (arithmeticSourceClassRelationStageHom Ω a ha P B c r)⟩

end
end Dubon2026

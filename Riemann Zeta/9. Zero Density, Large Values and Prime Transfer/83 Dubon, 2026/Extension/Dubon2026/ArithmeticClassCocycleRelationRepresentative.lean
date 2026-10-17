import Dubon2026.ArithmeticFreeClassHomCocycle
import Dubon2026.OriginalRelationHomFromCoboundary
import Dubon2026.ContinuousEquivariantCoefficientMap

/-! # Actual degree-one class cocycles have relation representatives

The original coefficient cocycle maps to a coboundary on its restricted
free cover. Restrict that actual lift to the relation lattice. This gives
the source relation morphism used by finite descent and the finite scalar
criterion on DUB-17's reverse-localization chain, with no class Ext premise.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance classRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance classRelationStageAlgebra : Algebra ℚ P := P.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

/-- The original finite-stage coefficient Hom into the actual full-class colimit. -/
abbrev arithmeticFiniteCoefficientClassHom :=
  (Rep.ihom (Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B)).obj
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance classRelationHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every original continuous class Hom cocycle yields a genuine relation
morphism and the exact free-cover coboundary lift that defines it. -/
theorem arithmeticClassHomCocycle_exists_relation_representative
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      ∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom (c.val g) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
  let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let U := arithmeticRelationFreeClassHom Ω a ha P B
  letI : TopologicalSpace U := ⊥
  letI : DiscreteTopology U := ⟨rfl⟩
  letI : @ContinuousSMul ℤ U U.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ U U.hV2.toSMul _ _ continuous_of_discreteTopology
  let f := originalInternalHomPrecomposition C X.g
  let d := continuousCoefficientCocycleOneMap
    (arithmeticFiniteCoefficientClassHom Ω a ha P B) U f.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply f) c
  obtain ⟨v, hv⟩ := arithmeticRelationFreeClassHomCocycle_exists_coboundary Ω a ha P B d
  obtain ⟨φ, hφ⟩ := originalRelationHom_exists_of_free_coboundary X C
    (fun g => c.val g) v hv
  exact ⟨v, φ, hφ, hv⟩

end
end Dubon2026

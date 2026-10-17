import Dubon2026.ArithmeticSourceIdeleCupImage
import Dubon2026.ArithmeticSourceRelationContinuousCupMaps

/-! # The original source-idele input of the constructed relation cup

These maps use the same finite coefficient and the same class-colimit
comparison as the enlarged relation obstruction. They serve the remaining
identification of its normalized readout with the source local cup sum.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleRelationFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

/-- Hom from the same restricted finite coefficient to the actual source ideles. -/
abbrev arithmeticFiniteCoefficientSourceIdeleHom :=
  arithmeticSourceIdeleHomRep ℚ Ω a ha (Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B)

variable [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationMapsLocalInstance1 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleRelationMapsLocalInstance2 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Send the actual source-idele Hom cocycle through the original quotient,
retaining the same finite coefficient used by the source relation data. -/
def arithmeticSourceIdeleCocycleQuotient :
    continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) →ₗ[ℤ]
      continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B) := by
  let A := Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B
  let q := (Rep.ihom A).map (arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha)
  exact continuousCoefficientCocycleOneMap _ _ q.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply q)

/-- The actual source ideles map to the identical full-class colimit used by
the constructed scalar relation obstruction. -/
def arithmeticSourceIdeleToFullClassColimit :
    arithmeticSPlaceColimitRep ℚ Ω a ha ⟶ arithmeticClassesModOutsideColimitRep ℚ Ω a ha :=
  arithmeticSPlaceColimitQuotientRepHom ℚ Ω a ha ≫ arithmeticSourceClassColimitComparison ℚ Ω a ha

end
end Dubon2026

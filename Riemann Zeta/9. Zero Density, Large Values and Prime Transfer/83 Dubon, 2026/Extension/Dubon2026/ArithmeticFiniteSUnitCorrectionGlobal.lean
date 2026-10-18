import Dubon2026.ArithmeticSourceIdeleExactSequence
import Dubon2026.OriginalRelationModuleSequence

/-! Carry the actual finite S-unit correction into the original arithmetic
S-units and source ideles. This preserves the relation needed by the dual
connecting class on DUB-17's reverse H1 localization dependency chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K))

/-- The finite original relation morphism gives an equivariant morphism to
the actual arithmetic S-units through the literal finite-stage inclusion. -/
def arithmeticFiniteSUnitRelationToGlobal
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F) :
    Rep.res (AlgEquiv.restrictNormalHom F :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))
      (originalRelationModule B) ⟶ originalArithmeticSUnitRepresentation K Ω a ha :=
  (Rep.resFunctor (AlgEquiv.restrictNormalHom F :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))).map η ≫
      arithmeticSUnitFiniteStageInclusion K Ω a ha F

/-- The actual global diagonal retains the finite correction identity;
no global relation-compatibility hypothesis is required. -/
theorem arithmeticFiniteSUnitCorrection_global_relation
    (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha F)
    (l : Rep.free ℤ Gal(F/K) B ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha F)
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep K Ω a ha F)
    (hη : η ≫ arithmeticSPlaceFiniteStagePrincipal K Ω a ha F =
      φ - originalRelationInclusion B ≫ l) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
      AlgEquiv.restrictNormalHom F
    let j := coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceStageTransition K Ω a ha) F
    arithmeticFiniteSUnitRelationToGlobal K Ω a ha F B η ≫ arithmeticSourcePrincipalRepHom K Ω a ha =
      (Rep.resFunctor π).map φ ≫ j -
        (Rep.resFunctor π).map (originalRelationInclusion B) ≫ ((Rep.resFunctor π).map l ≫ j) := by
  intro π j
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun m => m.hom x) hη
  exact (arithmeticSourcePrincipal_finiteStage K Ω a ha F (η.hom x)).trans
    ((congrArg j.hom h).trans (map_sub j.hom _ _))

end
end Dubon2026

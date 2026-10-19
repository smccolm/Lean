import Dubon2026.ArithmeticLocalDualTowerDiagram
import Dubon2026.ArithmeticSPlaceLocalTower
import Mathlib.RepresentationTheory.Invariants

/-! The actual finite S-place relation transition gives the same local
invariant under the native dual presentation tower. This joins DUB-17's
finite correction to its original source-local relation, with the group
change, prime projection and completion comparison all constructed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) (p : rationalArithmeticExceptionalPrimes a ha)
  (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha M)

/-- Exact local invariant comparison for the original finite S-place relation. -/
abbrev ArithmeticSPlaceLocalRelationInvariantTowerCompatibility : Prop :=
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra;
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule;
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul;
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M;
    let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom;
    let πM := (AlgEquiv.restrictNormalHom M : rationalArithmeticGaloisGroup a →* Gal(M/ℚ)).comp j;
    let πL := (AlgEquiv.restrictNormalHom L : rationalArithmeticGaloisGroup a →* Gal(L/ℚ)).comp j;
    let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
      arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML;
    let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p;
    let ψL := (Rep.resFunctor πL).map φL ≫ rationalArithmeticSPlaceLocalMorphism a ha L p;
    let d := arithmeticLocalDualTowerDiagram a M L hML B p.val.val p.val.property;
    d.τ₃.hom ((Representation.linHom.invariantsEquivRepHom _ _).symm ψM).val =
      ((Representation.linHom.invariantsEquivRepHom _ _).symm ψL).val

/-- The original finite S-place relation gives exactly the native
tower image of its localized dual invariant. -/
theorem rationalArithmeticSPlaceLocalRelationInvariant_tower :
    ArithmeticSPlaceLocalRelationInvariantTowerCompatibility a ha M L hML B p φ := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let πM := (AlgEquiv.restrictNormalHom M : rationalArithmeticGaloisGroup a →* Gal(M/ℚ)).comp j
  let πL := (AlgEquiv.restrictNormalHom L : rationalArithmeticGaloisGroup a →* Gal(L/ℚ)).comp j
  let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
    arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
  let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p
  let ψL := (Rep.resFunctor πL).map φL ≫ rationalArithmeticSPlaceLocalMorphism a ha L p
  let d := arithmeticLocalDualTowerDiagram a M L hML B p.val.val p.val.property
  apply LinearMap.ext
  intro x
  change rationalArithmeticSPlaceLocalMap a ha M p
      (φ.hom ((originalRelationGroupChange τ B).hom x)) =
    rationalArithmeticSPlaceLocalMap a ha L p
      ((arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML).hom
        (φ.hom ((originalRelationGroupChange τ B).hom x)))
  exact (rationalArithmeticSPlaceLocalMap_tower a ha M L hML p
    (φ.hom ((originalRelationGroupChange τ B).hom x))).symm

end
end Dubon2026

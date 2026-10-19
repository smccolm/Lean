import Dubon2026.ArithmeticSPlaceLocalRelationInvariantTower
import Dubon2026.ArithmeticLocalDualTowerConnecting
import Dubon2026.ArithmeticPrimeUnitHomTowerH1

/-! The actual larger-field S-place relation has the same local dual
class under the proved backwards tower identification. This removes the
field-tower obstacle between the finite correction and the recovered
source-field local classes on DUB-17's reverse-localization chain. -/
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
  (B : Rep.{0} ℤ Gal(M/ℚ)) [Finite B] (p : rationalArithmeticExceptionalPrimes a ha)
  (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha M)

variable (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)

/-- The exact backwards tower identity for the actual S-place dual class. -/
abbrev ArithmeticSPlaceDualClassTowerCompatibility : Prop :=
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : Module.Finite ℤ BL := Module.Finite.of_finite
    let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let πM := (AlgEquiv.restrictNormalHom M : rationalArithmeticGaloisGroup a →* Gal(M/ℚ)).comp j
    let πL := (AlgEquiv.restrictNormalHom L : rationalArithmeticGaloisGroup a →* Gal(L/ℚ)).comp j
    let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
      arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
    let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p
    let ψL := (Rep.resFunctor πL).map φL ≫ rationalArithmeticSPlaceLocalMorphism a ha L p
    let wM := (Representation.linHom.invariantsEquivRepHom _ _).symm ψM
    let wL := (Representation.linHom.invariantsEquivRepHom _ _).symm ψL
    arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p.val.val p.val.property
      (arithmeticPrimeLocalUnitDualConnecting a L BL p.val.val p.val.property q (fun b => hCoeff b) wL) =
      arithmeticPrimeLocalUnitDualConnecting a M B p.val.val p.val.property q hCoeff wM

/-- The native connecting square and literal S-place invariant comparison
identify the larger-field local class with the source-field local class. -/
theorem rationalArithmeticSPlaceDualClass_tower :
    ArithmeticSPlaceDualClassTowerCompatibility a ha M L hML B p φ q hCoeff := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ BL := Module.Finite.of_finite
  let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let πM := (AlgEquiv.restrictNormalHom M : rationalArithmeticGaloisGroup a →* Gal(M/ℚ)).comp j
  let πL := (AlgEquiv.restrictNormalHom L : rationalArithmeticGaloisGroup a →* Gal(L/ℚ)).comp j
  let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
    arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
  let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p
  let ψL := (Rep.resFunctor πL).map φL ≫ rationalArithmeticSPlaceLocalMorphism a ha L p
  let wM := (Representation.linHom.invariantsEquivRepHom _ _).symm ψM
  let wL := (Representation.linHom.invariantsEquivRepHom _ _).symm ψL
  let d := arithmeticLocalDualTowerDiagram a M L hML B p.val.val p.val.property
  let YL := arithmeticPrimeLocalUnitDualSequence a L BL p.val.val p.val.property
  let wT : YL.X₃.ρ.invariants := ⟨d.τ₃.hom wM.val, fun g =>
    (Rep.hom_comm_apply d.τ₃ g wM.val).symm.trans (congrArg d.τ₃.hom (wM.property g))⟩
  have hw : wT = wL := Subtype.ext
    (rationalArithmeticSPlaceLocalRelationInvariant_tower a ha M L hML B p φ)
  have hc := arithmeticLocalDualConnecting_tower a q M L hML B hCoeff p.val.val p.val.property wM
  have hc' := hc.trans (congrArg
    (arithmeticPrimeLocalUnitDualConnecting a L BL p.val.val p.val.property q (fun b => hCoeff b)) hw)
  exact (congrArg (arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p.val.val p.val.property) hc').symm.trans
    (arithmeticPrimeUnitHomTowerH1Equiv_map a M L hML B p.val.val p.val.property
      (arithmeticPrimeLocalUnitDualConnecting a M B p.val.val p.val.property q hCoeff wM))

end
end Dubon2026

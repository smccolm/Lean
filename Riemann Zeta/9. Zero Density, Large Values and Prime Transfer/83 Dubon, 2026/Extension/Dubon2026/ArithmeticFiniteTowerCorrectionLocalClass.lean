import Dubon2026.ArithmeticFiniteCorrectionLocalClass
import Dubon2026.ArithmeticFiniteSUnitTowerLocalization
import Dubon2026.ArithmeticSPlaceDualClassTower

/-! The actual larger-field finite correction constructs a global
unit-Hom class whose original-prime localization is the same source-field
S-place connecting class. This composes global/local tower naturality,
principal comparison, free-correction removal and actual S-place descent
on DUB-17's route to prescribed global trace-dual restrictions. -/
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

attribute [local instance] arithmeticLocalConnectingAlgebraicClosure
variable (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The exact source-field local class of the returned finite correction. -/
abbrev ArithmeticFiniteTowerCorrectionLocalClassCompatibility : Prop :=
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
    let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
      arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
    let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p
    let wM := (Representation.linHom.invariantsEquivRepHom _ _).symm ψM
    ∀ (l : Rep.free ℤ Gal(L/ℚ) BL ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L)
      (η : originalRelationModule BL ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha L =
      φL - originalRelationInclusion BL ≫ l →
    arithmeticFiniteSUnitLocalH1Map a ha M B p.val.val p.val.property
      (arithmeticFiniteSUnitHomTowerH1Equiv a ha M L hML B
        (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa L BL
          (fun b => hCoeff b) η)) =
      arithmeticPrimeLocalUnitDualConnecting a M B p.val.val p.val.property q hCoeff wM

/-- The actual finite correction localizes to the original source-field
S-place dual class after the literal global tower identification. -/
theorem arithmeticFiniteTowerCorrection_local_class :
    ArithmeticFiniteTowerCorrectionLocalClassCompatibility a ha M L hML B p φ q hCoeff hqa := by
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
  let φL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
    arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML
  let ψM := (Rep.resFunctor πM).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha M p
  let wM := (Representation.linHom.invariantsEquivRepHom _ _).symm ψM
  change ∀ (l : Rep.free ℤ Gal(L/ℚ) BL ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L)
      (η : originalRelationModule BL ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha L),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha L =
      φL - originalRelationInclusion BL ≫ l →
    arithmeticFiniteSUnitLocalH1Map a ha M B p.val.val p.val.property
      (arithmeticFiniteSUnitHomTowerH1Equiv a ha M L hML B
        (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa L BL
          (fun b => hCoeff b) η)) =
      arithmeticPrimeLocalUnitDualConnecting a M B p.val.val p.val.property q hCoeff wM
  intro l η hη
  let x := arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa L BL
    (fun b => hCoeff b) η
  exact (arithmeticFiniteSUnitTowerH1_localization a ha M L hML B p.val.val p.val.property x).trans
    ((congrArg (arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p.val.val p.val.property)
      (arithmeticFiniteCorrection_local_class a ha L p BL q hqa (fun b => hCoeff b) φL l η hη)).trans
      (rationalArithmeticSPlaceDualClass_tower a ha M L hML B p φ q hCoeff))

end
end Dubon2026

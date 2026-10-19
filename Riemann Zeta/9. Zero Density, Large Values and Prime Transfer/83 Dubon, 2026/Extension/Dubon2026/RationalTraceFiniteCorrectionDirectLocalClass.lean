import Dubon2026.RationalTraceFiniteCorrectionDirectDualClass
import Dubon2026.RationalTraceFiniteSUnitNormalizedLocalization
import Dubon2026.ArithmeticFiniteTowerCorrectionLocalClass

/-! The actual direct global trace-dual class has the source-field
S-place local class under the proved arithmetic normalization. This joins
the finite correction to the prescribed source-class recovery on DUB-17's
reverse H1 localization chain, retaining the original trace classes. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F N : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hFN : F.toIntermediateField ≤ N.toIntermediateField)
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

attribute [local instance] rationalTraceFiniteDualClassAlgebraicClosure

attribute [local instance 1100] Submodule.module Submodule.Quotient.module
attribute [local instance] finiteGlobalTraceHomTopology finiteGlobalTraceHomDiscrete
  finiteGlobalTraceHomContinuousSMul originalGlobalTraceHomTopology originalGlobalTraceHomDiscrete
  originalGlobalTraceHomContinuousSMul finiteLocalTraceCoefficientFinite
  finiteLocalTraceCoefficientModuleFinite finiteLocalTraceHomTopology finiteLocalTraceHomDiscrete
  finiteLocalTraceHomContinuousSMul finiteLocalPrimeHomTopology finiteLocalPrimeHomDiscrete
  finiteLocalPrimeHomContinuousSMul exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete
variable (p : rationalArithmeticExceptionalPrimes a ha)

/-- The exact normalized original trace-dual restriction of the finite-correction class. -/
abbrev RationalTraceFiniteCorrectionDirectLocalClassCompatibility : Prop :=
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : Module F N := Algebra.toModule
    letI : SMul F N := Algebra.toSMul
    let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
    let B := rationalTraceOriginalFiniteRep a q σ F hker
    let BN := Rep.res τ B
    letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
    letI : Finite BN := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
    let hB : ∀ b : B, q • b = 0 := fun b => by
      simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    ∀ (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
      (l : Rep.free ℤ Gal(N/ℚ) BN ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N)
      (η : originalRelationModule BN ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha N =
      (originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
        arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha F N hFN) -
          originalRelationInclusion BN ≫ l →
    rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ
          (rationalTraceFiniteCorrectionDirectDualClass a ha q σ F N hFN hker hσ hqa hn η)) =
    rationalTraceFiniteLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn
      (arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hB
        ((Representation.linHom.invariantsEquivRepHom _ _).symm
          ((Rep.resFunctor π).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p)))

/-- The returned finite correction determines the actual original trace-dual
restriction through its source-field S-place dual connecting class. -/
theorem rationalTraceFiniteCorrectionDirect_local_class :
    RationalTraceFiniteCorrectionDirectLocalClassCompatibility
      a ha q σ F N hFN hker hσ hqa hn p := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Module F N := Algebra.toModule
  letI : SMul F N := Algebra.toSMul
  let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let BN := Rep.res τ B
  letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  letI : Finite BN := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  let hB : ∀ b : B, q • b = 0 := fun b => by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
    (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  change ∀ (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
      (l : Rep.free ℤ Gal(N/ℚ) BN ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N)
      (η : originalRelationModule BN ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha N =
      (originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
        arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha F N hFN) -
          originalRelationInclusion BN ≫ l →
    rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ
          (rationalTraceFiniteCorrectionDirectDualClass a ha q σ F N hFN hker hσ hqa hn η)) =
    rationalTraceFiniteLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn
      (arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hB
        ((Representation.linHom.invariantsEquivRepHom _ _).symm
          ((Rep.resFunctor π).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p)))
  intro φ l η hη
  let x : ArithmeticFiniteSUnitHomH1 a ha N BN :=
    arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa N BN (fun b => hB b) η
  let y : RationalTraceFiniteSUnitHomH1 a ha q σ F hker :=
    arithmeticFiniteSUnitHomTowerH1Equiv a ha F N hFN B x
  have ht := rationalTraceFiniteSUnitH1_normalized_localization a ha q σ F hker hσ hqa hn
    p.val.val p.val.property y
  have hl := arithmeticFiniteTowerCorrection_local_class a ha F N hFN B p φ q hB hqa l η hη
  exact ht.trans (congrArg
    (rationalTraceFiniteLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn) hl)

end
end Dubon2026

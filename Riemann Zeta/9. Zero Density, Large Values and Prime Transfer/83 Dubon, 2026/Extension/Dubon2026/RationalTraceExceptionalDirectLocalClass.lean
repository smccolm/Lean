import Dubon2026.RationalTraceFiniteCorrectionDirectLocalClass
import Dubon2026.RationalTraceExceptionalSPlaceDualClass

/-! Apply the original global-class localization theorem to the actual
assembled exceptional S-place relation. Its local class is precisely the
one recovered from the retained source cups on DUB-17's chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois



attribute [local instance] rationalExceptionalIndexedPrimeLiesOver
  finiteLocalTraceCoefficientFinite finiteLocalTraceCoefficientModuleFinite
  finiteLocalTraceHomTopology finiteLocalTraceHomDiscrete finiteLocalTraceHomContinuousSMul
  finiteLocalPrimeHomTopology finiteLocalPrimeHomDiscrete finiteLocalPrimeHomContinuousSMul
  traceOriginalFiniteRepFinite traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)
  (ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    Rep.res (originalAdicCompletionGaloisInclusion ℚ F
      (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (originalRelationModule (rationalTraceOriginalFiniteRep a q σ F hker)) ⟶
    Rep.ofAlgebraAutOnUnits ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F))


variable (p : rationalArithmeticExceptionalPrimes a ha)


attribute [local instance] rationalTraceFiniteDualClassAlgebraicClosure
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete
attribute [local instance 1100] Submodule.module Submodule.Quotient.module
variable (N : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hFN : F.toIntermediateField ≤ N.toIntermediateField) (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The exact direct-class localization at the actual assembled source relation. -/
abbrev RationalTraceExceptionalDirectLocalClassCompatibility : Prop :=
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : Module F N := Algebra.toModule
    letI : SMul F N := Algebra.toSMul
    let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
    let B := rationalTraceOriginalFiniteRep a q σ F hker
    let BN := Rep.res τ B
    let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
    ∀ (l : Rep.free ℤ Gal(N/ℚ) BN ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N)
      (η : originalRelationModule BN ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha N =
      (originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map Φ ≫
        arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha F N hFN) -
          originalRelationInclusion BN ≫ l →
    rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ
          (rationalTraceFiniteCorrectionDirectDualClass a ha q σ F N hFN hker hσ hqa hn η)) =
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p

/-- The direct finite-correction class localizes to the actual assembled source class. -/
theorem rationalTraceExceptionalDirect_local_class :
    RationalTraceExceptionalDirectLocalClassCompatibility a ha q σ F hker hσ hn ψ p N hFN hqa := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Module F N := Algebra.toModule
  letI : SMul F N := Algebra.toSMul
  let τ : Gal(N/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let BN := Rep.res τ B
  let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
  change ∀ (l : Rep.free ℤ Gal(N/ℚ) BN ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N)
      (η : originalRelationModule BN ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha N),
    η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha N =
      (originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map Φ ≫
        arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha F N hFN) -
          originalRelationInclusion BN ≫ l →
    rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ
          (rationalTraceFiniteCorrectionDirectDualClass a ha q σ F N hFN hker hσ hqa hn η)) =
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p
  intro l η hη
  exact rationalTraceFiniteCorrectionDirect_local_class a ha q σ F N hFN hker hσ hqa hn p Φ l η hη

end
end Dubon2026

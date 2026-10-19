import Dubon2026.RationalTraceFiniteCompletionH1Comparison
import Dubon2026.RationalExceptionalSPlaceLocalConnecting

/-! The original exceptional S-place relation supplies an actual
prime-local trace-Hom H1 class. Its completion image is exactly the
original source-local connecting class, for DUB-17's prescribed-class
recovery using the retained source cups. -/
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

/-- The actual prime-local dual class of the assembled original S-place relation. -/
def rationalTraceExceptionalSPlaceLocalDualClass :
    ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property)))
      (rationalPrimeTraceUnitHomAction_continuous p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn) := by
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  have hB (b : B) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
    (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
  let φ := (Rep.resFunctor π).map Φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
  let w := (Representation.linHom.invariantsEquivRepHom _ _).symm φ
  let z := arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hB w
  exact rationalTraceFiniteLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn z

/-- The actual prime-local dual class maps to the original source-local
connecting class. Every coefficient and completion comparison is proved. -/
theorem rationalTraceExceptionalSPlaceLocalDualClass_completion :
    let B := rationalTraceOriginalFiniteRep a q σ F hker
    let hB : ∀ b : B, q • b = 0 := fun b => by
      simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
    rationalTraceOriginalLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn
      (rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p) =
      galoisTowerLocalUnitDualConnectingClass ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      B q hB (ψ p) := by
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  have hB (b : B) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
    (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let Φ := rationalExceptionalSPlaceRelation a ha F B ψ
  let φ := (Rep.resFunctor π).map Φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
  let w := (Representation.linHom.invariantsEquivRepHom _ _).symm φ
  let z := arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hB w
  exact (rationalTraceFiniteCompletionH1_comparison a q σ F hker
    p.val.val p.val.property hσ hn z).trans
    (rationalExceptionalSPlaceRelation_local_connecting a ha F B ψ q hB p)

end
end Dubon2026

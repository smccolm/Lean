import Dubon2026.RationalTraceOriginalSourceCupSeparation
import Dubon2026.RationalTraceCoherentSourceH1
import Dubon2026.RationalTraceExceptionalSPlaceDualClass
import Dubon2026.RationalTraceOriginalMappedCupSeparation
import Dubon2026.RationalTraceOriginalCartierH1Cup
import Dubon2026.GaloisTowerLocalUnitDualConnecting

/-! Recover the prescribed coherently normalized prime-local trace-dual
class from the actual assembled exceptional S-place relation. The retained
source cups are consumed through the proved forward comparison and native
perfect pairing, on DUB-17's reverse-localization chain. -/
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

attribute [local instance] primeTraceIntegerContinuousSMul
  traceOriginalCoefficientTopology traceOriginalCoefficientDiscrete traceOriginalCoefficientContinuousSMul
  localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete localRelationCupCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

attribute [local instance 1100] Submodule.module Submodule.Quotient.module

variable (hqa : (q : 𝓞 ℚ) ∣ a)

private theorem constructed_class_cup
    (z : galoisTowerLocalCoefficientH1 ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker)) :
    rationalTraceOriginalLocalUnitH1Cup a q σ F hker p.val.val p.val.property z
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn
        (rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p)) =
    galoisTowerLocalUnitRelationConnecting ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (ψ p) z := by
  have hB (b : rationalTraceOriginalFiniteRep a q σ F hker) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  exact (congrArg (fun x => rationalTraceOriginalLocalUnitH1Cup a q σ F hker p.val.val p.val.property z x)
    (rationalTraceExceptionalSPlaceLocalDualClass_completion a ha q σ F hker hσ hn ψ p)).trans
    (galoisTowerLocalUnitRelationConnecting_cup ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) q hB (ψ p) z).symm

/-- The retained original coefficient-first cup identities for the given
source cocycle and the actual exceptional local relation. -/
abbrev RationalTraceExceptionalSourceCupIdentity
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property) : Prop :=
  (∀ z : galoisTowerLocalCoefficientH1 ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker),
      galoisTowerLocalUnitCup ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (rationalTraceOriginalCartierAdicCocycle a q σ F hker p.val.val p.val.property hn c) z =
      galoisTowerLocalUnitRelationConnecting ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (ψ p) z)

/-- The retained source-local cups identify the actual assembled S-place
dual class with the prescribed coherent trace-dual class. All coefficient,
completion, connecting and perfect-pairing inputs have proved consumers. -/
abbrev RationalTraceExceptionalSPlaceSourceClassRecovery : Prop :=
    ∀ c : rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property,
    RationalTraceExceptionalSourceCupIdentity a ha q σ F hker hn ψ p c →
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p =
      rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
        (Submodule.Quotient.mk c)

private theorem class_eq_of_source_cups
    (v : ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property)))
      (rationalPrimeTraceUnitHomAction_continuous p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn))
    (h : ∀ z : galoisTowerLocalCoefficientH1 ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker),
      rationalTraceOriginalLocalUnitH1Cup a q σ F hker p.val.val p.val.property z
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn v) =
      galoisTowerLocalUnitRelationConnecting ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (ψ p) z) :
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p = v := by
  apply rationalTraceOriginalMappedHomH1_eq_of_source_cups a q σ F hker
    p.val.val p.val.property hσ hn
  intro z
  exact (constructed_class_cup a ha q σ F hker hσ hn ψ p z).trans (h z).symm

private theorem prescribed_class_cup
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)
    (h : RationalTraceExceptionalSourceCupIdentity a ha q σ F hker hn ψ p c)
    (z : galoisTowerLocalCoefficientH1 ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker)) :
    rationalTraceOriginalLocalUnitH1Cup a q σ F hker p.val.val p.val.property z
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p.val.val p.val.property hσ hn
        (rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
          (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
          (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
          (Submodule.Quotient.mk c))) =
      galoisTowerLocalUnitRelationConnecting ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (ψ p) z := by
  exact (rationalTraceOriginalCartierH1_cup a q σ F hker
    p.val.val p.val.property hσ hn c z).trans (h z)

/-- The actual source cup identities recover the prescribed coherently
normalized class without assuming a local identification. -/
theorem rationalTraceExceptionalSPlaceLocalDualClass_eq_source
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)
    (h : RationalTraceExceptionalSourceCupIdentity a ha q σ F hker hn ψ p c) :
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p =
      rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
        (Submodule.Quotient.mk c) := by
  exact class_eq_of_source_cups a ha q σ F hker hσ hn ψ p _
    (prescribed_class_cup a ha q σ F hker hσ hn ψ p c h)

/-- The retained source-local cups identify the actual assembled S-place
dual class with the prescribed coherent trace-dual class. All coefficient,
completion, connecting and perfect-pairing inputs have proved consumers. -/
abbrev RationalTraceExceptionalSPlaceClassRecovery : Prop :=
    ∀ c : rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property,
    (∀ z : galoisTowerLocalCoefficientH1 ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker),
      galoisTowerLocalUnitCup ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (rationalTraceOriginalCartierAdicCocycle a q σ F hker p.val.val p.val.property hn
        (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property c)) z =
      galoisTowerLocalUnitRelationConnecting ((rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)
      ((rationalExceptionalIndexedUpperPrime a ha F p).val.adicCompletion F)
      (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F
        (rationalExceptionalIndexedBasePrime a ha p) (rationalExceptionalIndexedUpperPrime a ha F p).val)
      (rationalTraceOriginalFiniteRep a q σ F hker) (ψ p) z) →
    rationalTraceExceptionalSPlaceLocalDualClass a ha q σ F hker hσ hn ψ p =
      rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
        (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
          Submodule.Quotient.mk c)

/-- The actual source cup identities recover the prescribed coherent
class with its arithmetic normalization, by the source-class identification. -/
theorem rationalTraceExceptionalSPlaceLocalDualClass_eq_coherent :
    RationalTraceExceptionalSPlaceClassRecovery a ha q σ F hker hσ hn ψ p hqa := by
  intro c h
  have hc := rationalTraceExceptionalSPlaceLocalDualClass_eq_source a ha q σ F hker hσ hn ψ p
    (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property c) h
  exact hc.trans (rationalTraceCoherentUnitH1_mk a q σ F hker p.val.val p.val.property hσ hn hqa c)

end
end Dubon2026

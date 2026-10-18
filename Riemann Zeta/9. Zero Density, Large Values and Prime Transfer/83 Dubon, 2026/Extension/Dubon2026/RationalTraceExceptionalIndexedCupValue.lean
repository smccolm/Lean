import Dubon2026.RationalTraceExceptionalFiniteCupValue
/-! Identify the actual indexed coherent Cartier cup with its original prime-local value. This is the representation boundary between DUB-17's constructed indexed relation total and source-annihilator cup sum. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois traceOriginalFiniteRepFinite rationalExceptionalIndexedPrimeLiesOver
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  (d : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)

attribute [local instance] traceExceptionalHomTopology traceExceptionalHomDiscrete
  traceExceptionalHomContinuousSMul


attribute [local instance] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)



/-- The literal indexed local Hom coefficient used by the relation total. -/
abbrev rationalTraceExceptionalIndexedLocalHomRep
    (p : rationalArithmeticExceptionalPrimes a ha) :=
  originalAdicLocalCoefficientUnitHom ℚ F (rationalExceptionalIndexedBasePrime a ha p)
    (rationalExceptionalIndexedUpperPrime a ha F p).val (rationalPrimeLocalClosure p.val.val p.val.property)
    (rationalTraceOriginalFiniteRep a q σ F hker)

/-- Retain the original discrete topology on the exact indexed Hom. -/
local instance indexedCoherentHomTopology (p : rationalArithmeticExceptionalPrimes a ha) :
    TopologicalSpace (rationalTraceExceptionalIndexedLocalHomRep a ha q σ F hker p) := ⊥

/-- The indexed Hom coefficient remains discrete. -/
local instance indexedCoherentHomDiscrete (p : rationalArithmeticExceptionalPrimes a ha) :
    DiscreteTopology (rationalTraceExceptionalIndexedLocalHomRep a ha q σ F hker p) := ⟨rfl⟩

/-- Original integer scalar multiplication is continuous on the indexed Hom. -/
local instance indexedCoherentHomContinuousSMul (p : rationalArithmeticExceptionalPrimes a ha) :
    @ContinuousSMul ℤ (rationalTraceExceptionalIndexedLocalHomRep a ha q σ F hker p)
      (rationalTraceExceptionalIndexedLocalHomRep a ha q σ F hker p).hV2.toSMul
      inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩

/-- The same original coherent Cartier values in the literal indexed
coefficient type consumed by the generic relation total. -/
def rationalTraceExceptionalIndexedCoherentCartierCocycle
    (p : rationalArithmeticExceptionalPrimes a ha) :
    continuousRepresentationCocyclesOne
      (rationalTraceExceptionalIndexedLocalHomRep a ha q σ F hker p) := by
  dsimp only [rationalTraceExceptionalIndexedLocalHomRep,
    rationalExceptionalIndexedBasePrime, rationalExceptionalIndexedUpperPrime]
  exact rationalTraceOriginalCartierAdicCocycle a q σ F hker p.val.val p.val.property hn
    (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p))

/-- The indexed family and original-prime notation give the same actual
finite-local cup invariant; no normalization equality is assumed. -/
theorem rationalTraceExceptionalCoherentFiniteCupValue_eq_indexed
    (p : rationalArithmeticExceptionalPrimes a ha)
    (x : rationalTraceExceptionalFiniteLocalH1 a ha q σ F hker p) :
    originalAdicFiniteLocalCupInvariant ℚ F (rationalExceptionalIndexedBasePrime a ha p)
      (rationalExceptionalIndexedUpperPrime a ha F p).val (rationalPrimeLocalClosure p.val.val p.val.property)
      (rationalTraceOriginalFiniteRep a q σ F hker)
      (rationalTraceExceptionalIndexedCoherentCartierCocycle a ha q σ F hker hn d hqa p) x =
      rationalTraceExceptionalCoherentFiniteCupValue a ha q σ F hker hn d hqa p x := by
  dsimp only [rationalTraceExceptionalIndexedCoherentCartierCocycle,
    rationalTraceExceptionalCoherentFiniteCupValue,
    rationalExceptionalIndexedBasePrime, rationalExceptionalIndexedUpperPrime]
  rfl

end
end Dubon2026

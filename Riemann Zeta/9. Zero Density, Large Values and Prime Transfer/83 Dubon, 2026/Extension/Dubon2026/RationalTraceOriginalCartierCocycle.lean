import Dubon2026.RationalTraceOriginalLocalHomCocycle
import Dubon2026.RationalPrimeTraceUnitCocycle
import Dubon2026.OriginalAdicLocalUnitCupRealization

/-! Actual local Cartier cocycles in the original completion relation.
This is the local specialization required by DUB-17, before finite-family
assembly and the canonical total comparison. -/
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

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)

attribute [local instance] traceOriginalFiniteRepFinite

/-- The actual prime-local unit Hom is given its original discrete topology. -/
local instance traceCartierOriginalHomTopology :
    TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))) := ⊥

/-- The actual local unit Hom topology is discrete. -/
local instance traceCartierOriginalHomDiscrete :
    DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))) := ⟨rfl⟩

attribute [local instance] traceOriginalSourceHomContinuousSMul
  traceOriginalTargetHomTopology traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul

variable (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The original prime-local trace-dual continuous cocycle type, retaining
its native coefficient structures and topology for the arithmetic consumer. -/
abbrev rationalTraceOriginalCartierSourceCocycles : Type :=
  continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)

/-- The original twisted trace cocycle is sent to the actual original-completion
unit Hom cocycle by Cartier duality and the proved completion-group map. -/
def rationalTraceOriginalCartierCocycleMap :
    rationalTraceOriginalCartierSourceCocycles a q σ p hp →
    continuousRepresentationCocyclesOne (rationalTraceOriginalLocalHomRep a q σ F hker p hp) :=
  fun c => rationalTraceOriginalLocalHomCocycleMap a q σ F hker p hp
    (rationalPrimeTraceUnitCocycleEquiv p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn c)

attribute [local instance] originalAdicRelationCupHomTopology
  originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul

/-- The same constructed Cartier cocycle in the literal original-adic
coefficient type and its native discrete topology. Both original fields
and the cocycle function are retained. -/
def rationalTraceOriginalCartierAdicCocycle
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom ℚ F
      (rationalOriginalPrimePlace p hp) (rationalArithmeticOriginalPrime a p hp F)
      (rationalPrimeLocalClosure p hp) (rationalTraceOriginalFiniteRep a q σ F hker)) :=
  ⟨(rationalTraceOriginalCartierCocycleMap a q σ F hker p hp hn c).val,
    (rationalTraceOriginalCartierCocycleMap a q σ F hker p hp hn c).property⟩

/-- The constructed original-adic cocycle has precisely the original
Cartier trace-dual value at the corresponding prime-local automorphism. -/
theorem rationalTraceOriginalCartierAdicCocycle_apply
    (c : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) :
    (rationalTraceOriginalCartierAdicCocycle a q σ F hker p hp hn c).val g =
      rationalPrimeTraceUnitDualEquiv p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn
        (c.val ((rationalOriginalCompletionGaloisEquiv p hp).symm g)) := rfl

end
end Dubon2026

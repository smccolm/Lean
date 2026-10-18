import Dubon2026.RationalTraceOriginalCartierCocycle
import Dubon2026.RationalExceptionalIndexedPrimes

/-! The actual exceptional-prime Cartier cocycle family in original
completion coefficients. This supplies the indexed S-place construction
for DUB-17 without changing any dependent completion parameter. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
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
  (c : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)

/-- The actual original-completion unit Hom at this exceptional-prime index. -/
abbrev rationalTraceExceptionalLocalHomRep (p : rationalArithmeticExceptionalPrimes a ha) :
    Rep ℤ Gal(rationalPrimeLocalClosure p.val.val p.val.property /
      (rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ) :=
  rationalTraceOriginalLocalHomRep a q σ F hker p.val.val p.val.property

/-- Retain the original discrete topology on this actual indexed Hom coefficient. -/
local instance traceExceptionalHomTopology (p : rationalArithmeticExceptionalPrimes a ha) :
    TopologicalSpace (rationalTraceExceptionalLocalHomRep a ha q σ F hker p) := ⊥

/-- The actual indexed Hom topology is discrete. -/
local instance traceExceptionalHomDiscrete (p : rationalArithmeticExceptionalPrimes a ha) :
    DiscreteTopology (rationalTraceExceptionalLocalHomRep a ha q σ F hker p) := ⟨rfl⟩

/-- Integer scalar multiplication is continuous on the same actual discrete Hom. -/
local instance traceExceptionalHomContinuousSMul (p : rationalArithmeticExceptionalPrimes a ha) :
    @ContinuousSMul ℤ (rationalTraceExceptionalLocalHomRep a ha q σ F hker p)
      (rationalTraceExceptionalLocalHomRep a ha q σ F hker p).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Each original exceptional-prime trace-dual cocycle gives its actual
original-completion Cartier cocycle, at the literal chosen upper prime. -/
def rationalTraceExceptionalCartierCocycle (p : rationalArithmeticExceptionalPrimes a ha) :
    continuousRepresentationCocyclesOne (rationalTraceExceptionalLocalHomRep a ha q σ F hker p) := by
  let d := rationalTraceOriginalCartierAdicCocycle a q σ F hker p.val.val p.val.property hn (c p)
  exact ⟨d.val, d.property⟩

/-- The actual exceptional-prime family retains every literal normalized
Cartier trace-dual value at the corresponding prime-local automorphism. -/
theorem rationalTraceExceptionalCartierCocycle_apply
    (p : rationalArithmeticExceptionalPrimes a ha)
    (g : Gal(rationalPrimeLocalClosure p.val.val p.val.property /
      (rationalExceptionalIndexedBasePrime a ha p).adicCompletion ℚ)) :
    (rationalTraceExceptionalCartierCocycle a ha q σ F hker hn c p).val g =
      rationalPrimeTraceUnitDualEquiv p.val.val p.val.property q
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property)) hn
        ((c p).val ((rationalOriginalCompletionGaloisEquiv p.val.val p.val.property).symm g)) :=
  rationalTraceOriginalCartierAdicCocycle_apply a q σ F hker p.val.val p.val.property hn (c p) g

end
end Dubon2026

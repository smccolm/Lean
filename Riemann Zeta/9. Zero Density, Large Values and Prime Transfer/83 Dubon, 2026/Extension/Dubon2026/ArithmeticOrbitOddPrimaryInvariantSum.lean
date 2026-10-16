import Dubon2026.ArithmeticOrbitCompletionInvariantTerm
import Dubon2026.ArithmeticOddPrimaryInvariantSum

/-! # Odd-primary reciprocity for the actual completion-invariant blocks

Apply the proved rational odd-primary reciprocity theorem to genuine
field corestriction, then substitute the exact Mackey completion sum.
This supplies the numerical zero-sum identity on DUB-17's number-field
route. Individual prime support is supplied separately by the original
finite-global localization theorem, not inferred from cancellation.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The original rational unit coefficients retain their actual discrete topology. -/
local instance arithmeticOrbitSumRationalTopology : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
/-- The specified rational unit topology is discrete. -/
local instance arithmeticOrbitSumRationalDiscrete : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
/-- The original relative unit coefficients retain their actual discrete topology. -/
local instance arithmeticOrbitSumUpperTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The specified original relative unit topology is discrete. -/
local instance arithmeticOrbitSumUpperDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩

/-- The genuine completion-invariant blocks of an actual odd-primary arithmetic class have finite rational-prime support and zero sum. -/
theorem rationalArithmeticOrbit_invariants_exists_support_sum_zero
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (hy : q ^ (r + 1) • (Submodule.Quotient.mk y : GaloisUnitContinuousH2
      (K := F) (Ω := rationalUnramifiedExtension a)) = 0) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∉ S, (∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F ω.out y) = 0) ∧
      (∑ p ∈ S, (∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F ω.out y)) = 0 := by
  let f (p : Nat.Primes) : AddCircle (1 : ℚ) := ∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F ω.out y
  let x := galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)
  have he (p : Nat.Primes) : rationalArithmeticUnitPrimeInvariant a p.val p.property x = f p :=
    rationalArithmeticUnitCorestriction_primeInvariant_terms a p.val p.property F y
  obtain ⟨S, hS, hsum⟩ := rationalArithmeticUnitCorestriction_exists_support_sum_zero
    a q r hq hq2 hqa F (Submodule.Quotient.mk y) hy
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    exact (he p).symm.trans (hS p hp)
  · exact (Finset.sum_congr rfl (fun p _ => (he p).symm)).trans hsum

end
end Dubon2026

import Dubon2026.ArithmeticOrbitCompletionInvariantTerm
import Dubon2026.ArithmeticOrbitPrimeBijection

/-! # The actual corestriction invariant indexed by every original prime

Use the proved exact Mackey-orbit / original-prime equivalence, together
with Mathlib's finite-sum reindexing. Every selected completion is the
genuine indexed prime by the already proved literal equivalence identity.
This gives DUB-17's original-prime-indexed invariant sum, without a prime
coverage, multiplicity or representative-independence hypothesis.
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

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- Genuine field corestriction has the sum of the actual localized invariants indexed by all original primes above p, with exactly one term for each prime. -/
theorem rationalArithmeticUnitCorestriction_primeInvariant_originalPrimes
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    letI : Fintype {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp} :=
      Fintype.ofEquiv (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F)) (rationalArithmeticOrbitPrimeEquiv a p hp F)
    rationalArithmeticUnitPrimeInvariant a p hp
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp},
        rationalArithmeticOrbitCompletionUnitInvariant a p hp F
          ((rationalArithmeticOrbitPrimeEquiv a p hp F).symm w).out y := by
  letI : Fintype {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp} :=
    Fintype.ofEquiv (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F)) (rationalArithmeticOrbitPrimeEquiv a p hp F)
  let f : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) → AddCircle (1 : ℚ) := fun ω =>
    rationalArithmeticOrbitCompletionUnitInvariant a p hp F ω.out y
  exact (rationalArithmeticUnitCorestriction_primeInvariant_terms a p hp F y).trans
    ((rationalArithmeticOrbitPrimeEquiv a p hp F).symm.sum_comp f).symm

end
end Dubon2026

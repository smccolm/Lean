import Dubon2026.ArithmeticOrbitCompletionStructures
import Dubon2026.LocalFieldSurjectiveBaseInvariant

/-! # The normalized invariant on each genuine original prime completion

All completion, closure, local-field and valuation-extension premises
are constructed from the actual arithmetic orbit. The existing invariant
is preserved by its literal completion equivalence. This removes the
individual local invariant comparison from DUB-17's reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitLocalGalois arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionClosureTower arithmeticOrbitCompletionSourceValuation
  arithmeticOrbitCompletionSourceLocalField arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]

/-- The actual completion equivalence preserves the original normalized continuous local invariant. -/
theorem rationalArithmeticOrbitCompletion_invariant
    (x : GaloisUnitContinuousH2 (K := rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (Ω := rationalPrimeLocalClosure p hp)) :
    localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitLocalField a p hp F c)
      (rationalPrimeLocalClosure p hp)
      (continuousGaloisUnitBaseChangeH2 (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalArithmeticOrbitLocalField a p hp F c)
        (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) x) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp) x :=
  localFieldContinuousInvariant_surjective_baseChange
    (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticOrbitCompletion_algebraMap_surjective a p hp F c) x

end
end Dubon2026

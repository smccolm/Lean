import Dubon2026.ArithmeticOrbitCorestrictionInvariantSum

/-! # The actual individual original-completion invariant

Name the literal existing normalized invariant of the original localized
cocycle. This definition changes no mathematical object or hypothesis;
it lets DUB-17's finite-sum and support proofs retain a checked interface
instead of repeatedly expanding all completed-field scalar structures.
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
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The existing normalized invariant of the actual original global cocycle localized at its genuine coset-induced prime completion. -/
def rationalArithmeticOrbitCompletionUnitInvariant
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    AddCircle (1 : ℚ) :=
  localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp)
    (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y))

/-- The named individual invariant is definitionally the same original completion-localization invariant. -/
theorem rationalArithmeticOrbitCompletionUnitInvariant_eq
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    rationalArithmeticOrbitCompletionUnitInvariant a p hp F c y =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y)) := rfl

variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The proved actual field-corestriction identity retains exactly the named genuine completion invariants as its summands. -/
theorem rationalArithmeticUnitCorestriction_primeInvariant_terms
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    rationalArithmeticUnitPrimeInvariant a p hp
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F),
        rationalArithmeticOrbitCompletionUnitInvariant a p hp F ω.out y :=
  rationalArithmeticUnitCorestriction_primeInvariant a p hp F y

end
end Dubon2026

import Dubon2026.ArithmeticOrbitCompletionInvariant
import Dubon2026.ArithmeticOrbitCompletionUnitComparison
import Dubon2026.ArithmeticOrbitUnitTraceInvariant

/-! # Each original Mackey summand has its genuine prime-completion invariant

Compose the proved orbit trace identity, literal global cocycle comparison
and normalized completion invariant transport. All compatible local-field
structures and stabilizer quotient finiteness are constructed. DUB-17's
remaining number-field reciprocity step is indexing these summands by
original primes and transferring the total invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
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

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Keep the same actual closure-unit topology over the original number-field completion. -/
local instance arithmeticOrbitCompletionCoefficientTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)))

/-- The retained original unit coefficient topology is discrete. -/
local instance arithmeticOrbitCompletionCoefficientDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)))

/-- The actual finite global stage makes its local orbit stabilizer quotient finite. -/
local instance arithmeticOrbitCompletionCosets :
    Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) c) := by
  let H := cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalArithmeticOrbitFixingSubgroup a F) c
  haveI : Finite (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ H) :=
    Subgroup.quotient_finite_of_isOpen H
      (cosetOrbitStabilizer_isOpen (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous
        (rationalArithmeticOrbitFixingSubgroup a F) F.fixingSubgroup_isOpen c)
  exact Fintype.ofFinite _

/-- The invariant of the literal arithmetic Mackey summand equals the original global class localized through its genuine number-field prime completion. -/
theorem rationalArithmeticOrbitUnitTrace_completion_invariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (rationalArithmeticOrbitUnitTrace a p hp F c y) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y)) := by
  have ht := rationalArithmeticOrbitUnitTrace_invariant a p hp F c y
  have hc := rationalArithmeticOrbitCompletionUnitCocycle_baseChange a p hp F c y
  have hm := continuousGaloisUnitBaseChangeH2_mk
    (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y)
  have he := hm.trans (congrArg
    (fun z : continuousRepresentationCocyclesTwo
      (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp)) =>
      (Submodule.Quotient.mk z : GaloisUnitContinuousH2
        (K := rationalArithmeticOrbitLocalField a p hp F c) (Ω := rationalPrimeLocalClosure p hp))) hc)
  have hi := rationalArithmeticOrbitCompletion_invariant a p hp F c
    (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y))
  exact ht.trans ((congrArg
    (localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitLocalField a p hp F c)
      (rationalPrimeLocalClosure p hp)) he).symm.trans hi)

end
end Dubon2026

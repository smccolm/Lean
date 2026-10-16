import Dubon2026.ArithmeticOrbitUnitCorestrictionComparison

/-! # The literal arithmetic orbit trace is genuine field corestriction

This equality connects the actual Mackey summands to the existing local
invariant/corestriction theorem on DUB-17's global reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [tA : TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [dA : DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [tF : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [dF : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [tB : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [dB : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

variable [hFinite : FiniteDimensional ℚ F]

/-- The literal Mackey orbit trace equals the actual orbit-field trace. -/
theorem rationalArithmeticOrbitUnitCorestriction_eq_field
    [iH : Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) c)]
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    @rationalArithmeticOrbitUnitTrace a p hp F c tA dA tF dF tB dB hFinite iH y =
      @rationalArithmeticOrbitFieldTrace a p hp F c tF dF tB dB hFinite y := by
  apply galoisUnitContinuousCorestriction_eq_subgroupTrace
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticOrbitLocalField a p hp F c) _ _
    (rationalArithmeticOrbitLocalField_fixingSubgroup a p hp F c).symm
  intro d e
  exact (rationalArithmeticOrbitLocalUnitCocycle_apply a p hp F c y d e).trans
    (rationalArithmeticOrbitUnitCocycle_eq_baseChange a p hp F c y d e).symm

end
end Dubon2026

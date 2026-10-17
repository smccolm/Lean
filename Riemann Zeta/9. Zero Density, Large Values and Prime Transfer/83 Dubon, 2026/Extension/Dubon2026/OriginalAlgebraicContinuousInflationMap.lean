import Dubon2026.OriginalFiniteH2ContinuousDescent

/-! # The literal finite algebraic to continuous inflation map

This is the composite of the existing same-cocycle comparison with actual
continuous inflation. Naming that composite keeps nested-field elaboration
small in the two-primary descent needed by DUB-17's class-generator route.
-/
namespace Dubon2026
noncomputable section

/-- Actual finite algebraic H2 inflates through its discrete representative
into continuous H2 of the same extension. -/
def originalAlgebraicContinuousInflation
    (K L U : Type) [Field K] [Field L] [Field U]
    [Algebra K L] [Algebra K U] [Algebra L U] [IsScalarTower K L U]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois K U]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)] :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := K) (Ω := U) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
  exact (continuousGaloisUnitBaseChangeH2 K K L U).comp
    (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).symm.toLinearMap

/-- Equality of actual finite inflations implies equality of the named
literal continuous composites. -/
theorem originalAlgebraicContinuousInflation_eq_of_finite
    (K E L M U : Type) [Field K] [Field E] [Field L] [Field M] [Field U]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra K U]
    [Algebra E M] [Algebra L M] [Algebra M U] [Algebra E U] [Algebra L U]
    [IsScalarTower K E M] [IsScalarTower K L M] [IsScalarTower K M U]
    [IsScalarTower K E U] [IsScalarTower K L U]
    [IsScalarTower E M U] [IsScalarTower L M U]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois K U]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2)
    (y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (h : groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (finiteGaloisUnitTowerInclusion K E M) 2 x =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y) :
    originalAlgebraicContinuousInflation K E U x =
      originalAlgebraicContinuousInflation K L U y := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
  exact originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq K E L M U x y h

end
end Dubon2026

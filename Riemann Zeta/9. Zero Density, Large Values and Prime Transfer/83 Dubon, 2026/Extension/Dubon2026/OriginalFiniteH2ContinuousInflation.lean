import Dubon2026.FiniteGaloisH2BaseChangeComparison

/-! # Original finite algebraic inflation and actual continuous inflation

The comparison preserves the same original cocycles. It lets the algebraic
cyclic descent equality enter the original continuous arithmetic extension,
as required by DUB-17's arithmetic invariant-sum source consumer.
-/
namespace Dubon2026
noncomputable section

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- The actual continuous finite-field inflation has exactly the original algebraic finite-tower H2 image. -/
theorem originalFiniteH2_continuousInflation_comparison
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := M))
      (finiteGaloisUnitBaseChangeH2 K K L M x) =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2
        (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitBaseChangeH2_mk, continuousDiscreteH2Equiv_mk,
      continuousDiscreteH2Equiv_mk, groupCohomology.H2π_comp_map_apply]
    rfl

end
end Dubon2026

import Dubon2026.FiniteGaloisH2BaseChangeComparison
import Dubon2026.FiniteGaloisUnitH2InflationRestriction
import Dubon2026.FiniteContinuousGaloisH2InflationInjection

/-! # Original finite Galois H2 classes descend exactly when actual base change vanishes -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
  [FiniteDimensional E M] [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- An original finite L/K class inflates from an actual E/K class in
the genuine common Galois extension exactly when its actual base change to
M/E vanishes. Actual Hilbert90 and exact inflation-restriction prove descent. -/
theorem finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    (∃ y : GaloisUnitContinuousH2 (K := K) (Ω := E),
      finiteGaloisUnitTowerH2Inflation K E M y = finiteGaloisUnitTowerH2Inflation K L M x) ↔
        finiteGaloisUnitBaseChangeH2 K E L M x = 0 := by
  let eE := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K E)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := E))
  let eL := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  let eM := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := M))
  let eEM := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
    (discreteGaloisUnitAction_continuous (K := E) (Ω := M))
  have hres : galoisUnitTowerH2Restriction K E M
      (eM (finiteGaloisUnitTowerH2Inflation K L M x)) =
        eEM (finiteGaloisUnitBaseChangeH2 K E L M x) := by
    change galoisUnitTowerH2Restriction K E M
      (continuousDiscreteH2Equiv _ _ (finiteGaloisUnitTowerH2Inflation K L M x)) =
        continuousDiscreteH2Equiv _ _ (finiteGaloisUnitBaseChangeH2 K E L M x)
    rw [continuousDiscreteH2Equiv_finiteGaloisInflation,
      continuousDiscreteH2Equiv_finiteGaloisBaseChange]
    exact congrArg (fun f : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits E M) 2 => f (eL x))
      (galoisUnitH2_inflation_restriction_baseChange K E L M)
  constructor
  · rintro ⟨y, hy⟩
    apply eEM.injective
    rw [map_zero, ← hres]
    apply (finiteGaloisUnitH2_inflation_exists_iff_restriction_zero K E M _).mp
    refine ⟨eE y, ?_⟩
    rw [← continuousDiscreteH2Equiv_finiteGaloisInflation K E M y, hy]
  · intro hx
    have hz : galoisUnitTowerH2Restriction K E M
        (eM (finiteGaloisUnitTowerH2Inflation K L M x)) = 0 := by
      rw [hres, hx, map_zero]
    obtain ⟨z, hz⟩ := (finiteGaloisUnitH2_inflation_exists_iff_restriction_zero K E M _).mpr hz
    obtain ⟨y, rfl⟩ := eE.surjective z
    refine ⟨y, eM.injective ?_⟩
    rw [continuousDiscreteH2Equiv_finiteGaloisInflation]
    exact hz

end
end Dubon2026

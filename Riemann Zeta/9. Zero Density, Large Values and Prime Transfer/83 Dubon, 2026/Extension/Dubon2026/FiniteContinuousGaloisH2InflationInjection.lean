import Dubon2026.FiniteGaloisUnitH2InflationInjection
import Dubon2026.ContinuousDiscreteH2Comparison

/-! # Actual continuous unit H2 inflation is injective in finite Galois towers -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- The original continuous-to-algebraic comparison commutes with the
literal field-tower inflation, through the same original cocycle values. -/
theorem continuousDiscreteH2Equiv_finiteGaloisInflation
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := M))
        (finiteGaloisUnitTowerH2Inflation K L M x) =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2
        (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitTowerH2Inflation_mk, continuousDiscreteH2Equiv_mk,
      continuousDiscreteH2Equiv_mk, groupCohomology.H2π_comp_map_apply]
    rfl

/-- The original continuous finite field-tower H2 inflation is
injective. The proof uses the same-cocycle comparison and the proved
actual algebraic inflation injection, with no inflation certificate. -/
theorem finiteGaloisUnitTowerH2Inflation_injective :
    Function.Injective (finiteGaloisUnitTowerH2Inflation K L M) := by
  haveI : FiniteDimensional L M := FiniteDimensional.right K L M
  have hinj := (ModuleCat.mono_iff_injective _).mp (finiteGaloisUnitH2Inflation_mono K L M)
  intro x y hxy
  apply (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).injective
  apply hinj
  rw [← continuousDiscreteH2Equiv_finiteGaloisInflation K L M,
    ← continuousDiscreteH2Equiv_finiteGaloisInflation K L M, hxy]

end
end Dubon2026

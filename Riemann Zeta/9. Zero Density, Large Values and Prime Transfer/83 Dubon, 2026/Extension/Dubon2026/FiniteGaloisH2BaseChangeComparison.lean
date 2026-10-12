import Dubon2026.GaloisUnitBaseChange
import Dubon2026.GaloisUnitTowerRestriction
import Dubon2026.ContinuousDiscreteH2Comparison

/-! # Same-cocycle comparisons for actual Galois H2 base change -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

/-- Original inflation followed by actual fixed-field restriction is
exactly the genuine base-change map, through identical original cochains. -/
theorem galoisUnitH2_inflation_restriction_baseChange :
    groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 ≫
      galoisUnitTowerH2Restriction K E M =
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains
      (Rep.ofAlgebraAutOnUnits K L) ⟶
      groupCohomology.inhomogeneousCochains (Rep.ofAlgebraAutOnUnits E M) =>
        HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

variable [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- The original continuous-to-algebraic comparison commutes with the
literal base-change map, preserving the same actual cocycle values. -/
theorem continuousDiscreteH2Equiv_finiteGaloisBaseChange
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits E M)
      (discreteGaloisUnitAction_continuous (K := E) (Ω := M))
      (finiteGaloisUnitBaseChangeH2 K E L M x) =
        groupCohomology.map (galoisBaseChangeRestriction K E L M)
          (galoisUnitBaseChangeInclusion K E L M) 2
          (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
            (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitBaseChangeH2_mk, continuousDiscreteH2Equiv_mk,
      continuousDiscreteH2Equiv_mk, groupCohomology.H2π_comp_map_apply]
    rfl

end
end Dubon2026

import Dubon2026.OriginalFiniteH2ContinuousInflation
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Original finite descent equality in the same continuous extension

Equal algebraic inflations in the actual finite compositum imply equal
continuous inflations in the actual common extension. The proved
same-cocycle comparison and literal tower composition supply this step
from cyclic descent to DUB-17's original arithmetic H2 class.
-/
namespace Dubon2026
noncomputable section

/-- Equality of original finite algebraic inflations retains the same classes after actual continuous inflation into their original common extension. -/
theorem originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq
    (K E L M U : Type) [Field K] [Field E] [Field L] [Field M] [Field U]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra K U]
    [Algebra E M] [Algebra L M] [Algebra M U] [Algebra E U] [Algebra L U]
    [IsScalarTower K E M] [IsScalarTower K L M] [IsScalarTower K M U]
    [IsScalarTower K E U] [IsScalarTower K L U]
    [IsScalarTower E M U] [IsScalarTower L M U]
    [FiniteDimensional K E] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K L] [IsGalois K M] [IsGalois K U]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2)
    (y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (h : groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (finiteGaloisUnitTowerInclusion K E M) 2 x =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y) :
    continuousGaloisUnitBaseChangeH2 K K E U
      ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K E)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := E))).symm x) =
      continuousGaloisUnitBaseChangeH2 K K L U
        ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).symm y) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K M) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K M) := ⟨rfl⟩
  let eE := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K E)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := E))
  let eL := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  have hm : finiteGaloisUnitBaseChangeH2 K K E M (eE.symm x) =
      finiteGaloisUnitBaseChangeH2 K K L M (eL.symm y) := by
    apply (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := M))).injective
    rw [originalFiniteH2_continuousInflation_comparison,
      originalFiniteH2_continuousInflation_comparison]
    simpa only [eE, eL, LinearEquiv.apply_symm_apply] using h
  have hu := congrArg (continuousGaloisUnitBaseChangeH2 K K M U) hm
  exact (continuousGaloisUnitBaseChangeH2_comp K K K E M U (eE.symm x)).symm.trans
    (hu.trans (continuousGaloisUnitBaseChangeH2_comp K K K L M U (eL.symm y)))

end
end Dubon2026

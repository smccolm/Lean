import Dubon2026.FiniteGaloisUnitTowerInflation

/-! # Original finite Galois H2 inflation composes along actual field towers -/

namespace Dubon2026
noncomputable section

variable (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower K L M] [IsScalarTower K L N]
  [IsScalarTower K M N] [IsScalarTower L M N]
  [FiniteDimensional K M] [FiniteDimensional K N]
  [IsGalois K L] [IsGalois K M] [IsGalois K N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K N)]

/-- Actual finite-tower H2 inflation is transitive. Both original
restriction arguments and the original unit coefficient inclusions compose. -/
theorem finiteGaloisUnitTowerH2Inflation_comp
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    finiteGaloisUnitTowerH2Inflation K M N (finiteGaloisUnitTowerH2Inflation K L M x) =
      finiteGaloisUnitTowerH2Inflation K L N x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitTowerH2Inflation_mk, finiteGaloisUnitTowerH2Inflation_mk,
      finiteGaloisUnitTowerH2Inflation_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change Units.map (algebraMap M N).toMonoidHom
        (Units.map (algebraMap L M).toMonoidHom
          (Additive.toMul (Rep.toAdditive (c.val
            (AlgEquiv.restrictNormalHom L (AlgEquiv.restrictNormalHom M z.1),
              AlgEquiv.restrictNormalHom L (AlgEquiv.restrictNormalHom M z.2)))))) =
      Units.map (algebraMap L N).toMonoidHom
        (Additive.toMul (Rep.toAdditive (c.val
          (AlgEquiv.restrictNormalHom L z.1, AlgEquiv.restrictNormalHom L z.2))))
    rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M z.1,
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M z.2]
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply L M N _).symm

end
end Dubon2026

import Dubon2026.FiniteGaloisUnitTowerInflation

/-! # Actual finite-stage inflation commutes with original field towers -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Original finite-stage inflation is unchanged by inserting an actual
larger finite Galois field. Restriction composition and literal field inclusions
prove the identity on the original continuous representatives. -/
theorem galoisUnitFiniteStageH2Inflation_tower
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitFiniteStageH2Inflation E x =
      galoisUnitFiniteStageH2Inflation F (finiteGaloisUnitTowerH2Inflation K E F x) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower E F Ω := .of_algebraMap_eq' rfl
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitTowerH2Inflation_mk,
      galoisUnitFiniteStageH2Inflation_mk, galoisUnitFiniteStageH2Inflation_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change Units.map E.toIntermediateField.val.toMonoidHom
        (Additive.toMul (Rep.toAdditive
          (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)))) =
      Units.map F.toIntermediateField.val.toMonoidHom
        (Units.map (algebraMap E F).toMonoidHom
          (Additive.toMul (Rep.toAdditive (c.val
            (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.1),
              AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.2))))))
    rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.1,
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.2]
    apply Units.ext
    rfl

end
end Dubon2026

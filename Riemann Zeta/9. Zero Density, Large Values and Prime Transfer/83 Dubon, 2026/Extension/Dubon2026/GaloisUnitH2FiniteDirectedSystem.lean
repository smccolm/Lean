import Dubon2026.FiniteGaloisUnitTowerComposition
import Mathlib.Algebra.Colimit.Module

/-! # The genuine finite Galois unit H2 directed system -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- Original finite-stage continuous Galois unit H2, with the genuine
Krull topology and the discrete topology on the original coefficients. -/
abbrev GaloisUnitH2FiniteStage (F : FiniteGaloisIntermediateField K Ω) :=
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  GaloisUnitContinuousH2 (K := K) (Ω := F)

/-- The transition map uses the actual inclusion of the original finite
fields and original Galois restriction in both cocycle variables. -/
def galoisUnitH2FiniteTransition (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F) :
    GaloisUnitH2FiniteStage K Ω E →ₗ[ℤ] GaloisUnitH2FiniteStage K Ω F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact finiteGaloisUnitTowerH2Inflation K E F

/-- The actual transition on the same original field is the identity. -/
theorem galoisUnitH2FiniteTransition_self (E : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω E) :
    galoisUnitH2FiniteTransition K Ω E E le_rfl x = x := by
  letI : Algebra E E := (IntermediateField.inclusion (le_refl E.toIntermediateField)).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  have hj (g : Gal(E/K)) : AlgEquiv.restrictNormalHom E g = g := by
    apply AlgEquiv.ext
    intro x
    exact AlgEquiv.restrictNormal_commutes g E x
  change finiteGaloisUnitTowerH2Inflation K E E x = x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitTowerH2Inflation_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change Units.map (algebraMap E E).toMonoidHom
        (Additive.toMul (Rep.toAdditive
          (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)))) =
      Additive.toMul (Rep.toAdditive (c.val z))
    rw [hj, hj]
    apply Units.ext
    rfl

/-- Actual transition maps compose for inclusions of the original fields. -/
theorem galoisUnitH2FiniteTransition_comp (E F H : FiniteGaloisIntermediateField K Ω)
    (hEF : E ≤ F) (hFH : F ≤ H) (x : GaloisUnitH2FiniteStage K Ω E) :
    galoisUnitH2FiniteTransition K Ω F H hFH
        (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      galoisUnitH2FiniteTransition K Ω E H (hEF.trans hFH) x := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Algebra E H := (IntermediateField.inclusion (hEF.trans hFH)).toAlgebra
  haveI : IsScalarTower E F H := .of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K H) := ⟨rfl⟩
  exact finiteGaloisUnitTowerH2Inflation_comp K E F H x

/-- The original H2 transition maps satisfy both directed-system laws. -/
instance galoisUnitH2FiniteDirectedSystem :
    DirectedSystem (GaloisUnitH2FiniteStage K Ω)
      (fun E F h => galoisUnitH2FiniteTransition K Ω E F h) where
  map_self := fun {E} x => galoisUnitH2FiniteTransition_self K Ω E x
  map_map := fun {H F E} hEF hFH x =>
    galoisUnitH2FiniteTransition_comp K Ω E F H hEF hFH x

end
end Dubon2026

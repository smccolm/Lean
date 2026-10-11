import Dubon2026.GaloisUnitH2FiniteDirectedSystem
import Dubon2026.GaloisUnitFiniteStageTower

/-! # The actual finite-stage H2 colimit maps to original continuous Galois H2 -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [DecidableEq (FiniteGaloisIntermediateField K Ω)]

/-- The genuine module direct limit of original finite Galois unit H2
under the proved original inflation transition maps. -/
abbrev GaloisUnitH2FiniteColimit :=
  Module.DirectLimit (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω)

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Original finite-stage inflation with the actual discrete finite coefficients. -/
def galoisUnitH2FiniteStageMap (F : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω F →ₗ[ℤ] GaloisUnitContinuousH2 (K := K) (Ω := Ω) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact galoisUnitFiniteStageH2Inflation F

omit [DecidableEq (FiniteGaloisIntermediateField K Ω)] in
/-- Original finite-stage maps respect the actual directed-system transitions. -/
theorem galoisUnitH2FiniteStageMap_transition (E F : FiniteGaloisIntermediateField K Ω)
    (hEF : E ≤ F) (x : GaloisUnitH2FiniteStage K Ω E) :
    galoisUnitH2FiniteStageMap K Ω F (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      galoisUnitH2FiniteStageMap K Ω E x := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact (galoisUnitFiniteStageH2Inflation_tower E F hEF x).symm

/-- The actual universal map from the original finite-stage colimit to
the existing continuous H2 of the original infinite Galois extension. -/
def galoisUnitH2FiniteColimitToH2 :
    GaloisUnitH2FiniteColimit K Ω →ₗ[ℤ] GaloisUnitContinuousH2 (K := K) (Ω := Ω) :=
  Module.DirectLimit.lift ℤ (FiniteGaloisIntermediateField K Ω)
    (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω)
    (galoisUnitH2FiniteStageMap K Ω) (galoisUnitH2FiniteStageMap_transition K Ω)

/-- Each actual colimit representative maps to its original finite-stage inflation. -/
theorem galoisUnitH2FiniteColimitToH2_of (F : FiniteGaloisIntermediateField K Ω)
    (x : GaloisUnitH2FiniteStage K Ω F) :
    galoisUnitH2FiniteColimitToH2 K Ω
      (Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField K Ω)
        (GaloisUnitH2FiniteStage K Ω) (galoisUnitH2FiniteTransition K Ω) F x) =
      galoisUnitH2FiniteStageMap K Ω F x := by
  exact Module.DirectLimit.lift_of _ _ x

end
end Dubon2026

import Dubon2026.GaloisUnitBaseChangeComposition
import Dubon2026.GaloisUnitH2FiniteColimitMap

/-! # Original finite-stage inflation is actual continuous Galois base change -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original finite-stage inflation is the same original group
restriction and coefficient inclusion used by continuous base change. -/
theorem continuousGaloisUnitBaseChangeH2_eq_finiteStage
    (F : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K K F Ω x = galoisUnitH2FiniteStageMap K Ω F x := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change continuousGaloisUnitBaseChangeH2 K K F Ω (Submodule.Quotient.mk c) =
      galoisUnitFiniteStageH2Inflation F (Submodule.Quotient.mk c)
    rw [continuousGaloisUnitBaseChangeH2_mk, galoisUnitFiniteStageH2Inflation_mk]
    congr 1

end
end Dubon2026

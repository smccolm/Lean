import Dubon2026.ContinuousGaloisUnitH2FiniteStage
import Dubon2026.ContinuousGaloisUnitFiniteStageInjection

/-! # Original continuous unit-H2 descent retains its annihilator

Existing genuine finite descent and injective inflation give the finite
torsion class needed to apply the proved original cyclic killing theorem
to DUB-17's actual arithmetic Kummer image.
-/
namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- A constructed original finite Galois presentation retains the actual continuous class and its original annihilator. -/
theorem continuousGaloisUnitH2_exists_torsion_finite_stage
    (q : ℕ) (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) (hx : q • x = 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F), q • y = 0 ∧
        galoisUnitFiniteStageH2Inflation F y = x := by
  obtain ⟨F, y, hy⟩ := continuousGaloisUnitH2_exists_finite_stage x
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  refine ⟨F, y, ?_, hy⟩
  apply galoisUnitFiniteStageH2Inflation_injective F
  rw [map_nsmul, map_zero, hy, hx]

end
end Dubon2026

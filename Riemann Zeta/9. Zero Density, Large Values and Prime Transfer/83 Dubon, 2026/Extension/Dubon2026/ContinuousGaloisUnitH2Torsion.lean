import Dubon2026.ContinuousGaloisUnitH2FiniteStage
import Dubon2026.ContinuousFiniteH2CardAnnihilation

/-! # Every original continuous Galois unit H2 class is torsion -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- An original continuous unit H2 class comes from an actual finite Galois
stage. That original finite group's positive order kills the class by the
proved undivided continuous sum identity, and genuine inflation preserves it. -/
theorem continuousGaloisUnitH2_is_torsion
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  obtain ⟨F, hF⟩ := continuousGaloisUnitH2_exists_finite_stage x
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  obtain ⟨y, hy⟩ := hF
  letI : Fintype Gal(F/K) := Fintype.ofFinite _
  refine ⟨Fintype.card Gal(F/K), Fintype.card_pos, ?_⟩
  rw [← hy, ← map_nsmul]
  rw [continuousFiniteH2_card_nsmul_eq_zero (Rep.ofAlgebraAutOnUnits K F)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := F)) y, map_zero]

end
end Dubon2026

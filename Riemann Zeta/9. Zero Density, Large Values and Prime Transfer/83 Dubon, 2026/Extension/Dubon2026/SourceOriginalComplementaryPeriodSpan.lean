import Dubon2026.SourceOriginalRegularLoopJumpClosure
import Dubon2026.SourceOriginalDiscretePeriodsOfLoops

/-! DUB-17/18 -> original Abel-Jacobi -> unimodular period matrix.
The actual complementary loop periods span the full real coordinate space.
Use proved regular-loop generation and the original full-real-span theorem;
no independent period-basis or span assumption is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem complementary_periods_span_real (D : CellDissection N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hR : RegularCycleGeneration D (fun i => (b i : Ω[F⁄ℂ])) T Ts γ) :
    ⊤ ≤ Submodule.span ℝ (range (fun l : {l // l ∈ (T ∪ Ts)ᶜ} =>
      fun i => pathIntegral N (b i : Ω[F⁄ℂ]) (γ l.1))) := by
  let Pz : {l // l ∈ (T ∪ Ts)ᶜ} → Place ℂ F := fun l => D.vert (D.ends l.1).1
  let Z : ∀ l, Path (Pz l) (Pz l) := fun l => γ l.1
  have hL := original_period_lattice_eq_span_loops N
    (fun i => (b i : Ω[F⁄ℂ])) Pz Z (fun P δ => by
      obtain ⟨a, ha⟩ := hR P δ
      refine ⟨fun l => a l.1, fun i => ?_⟩
      rw [ha i, ← Finset.sum_coe_sort])
  rw [← Submodule.span_span_of_tower ℤ ℝ, ← hL,
    span_real_pathPeriodLattice_eq_top N b]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods

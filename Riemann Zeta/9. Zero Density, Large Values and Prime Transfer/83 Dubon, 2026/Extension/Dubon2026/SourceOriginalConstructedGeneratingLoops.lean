import Dubon2026.SourceOriginalGeneratingLoopReindex

/-! DUB-17/18 -> original Abel-Jacobi -> discrete original period lattice.
Construct the exact source number of actual loop generators for every original
regular-differential basis, using the proved finite cell dissection, Euler count,
integer cycles and arbitrary regular-loop generation. No geometric witness or
generation assumption is supplied by the caller.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential CellGeometry
attribute [local instance] placeTopology placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_generating_loops {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k)),
      ∀ (P : Place ℂ F) (δ : Path P P), ∃ a : Fin n ⊕ Fin n → ℤ, ∀ i,
        pathIntegral N (b i : Ω[F⁄ℂ]) δ =
          ∑ k, (a k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k) := by
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  obtain ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen, hW, hR⟩ := exists_original_regular_cycle_generation.{0, 0} P₀ ∅
      (fun i => (b i : Ω[F⁄ℂ])) (fun i => (b i).2)
  have hn : Module.finrank ℂ (regularDifferentials ℂ F) = n := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  rw [hn] at hc
  exact DissectionPeriods.exists_reindexed_cycle_periods A.dissection
    (fun i => (b i : Ω[F⁄ℂ])) T Ts hc γ hR

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalJSheetNeighborhoods
import Dubon2026.SourceOriginalUnramifiedChartDerivative
import Dubon2026.SourceOriginalAnalyticCellCoordinates

/-! DUB-17/18 -> geometric cell dissection -> analytic ordinary grid cells.
Every actual ordinary j sheet has analytic nonsingular transitions to the
original charts. The source equality with actual evaluation and the proved
order-one derivative lemma derive both analytic-cell fields.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The actual ordinary j sheet, equipped with its derived analytic coordinate fields. -/
def IsOriginalSheetFamily.analyticJCoord {ι : Type*} {V : Set ℂ}
    {ζ : ι → OpenPartialHomeomorph (Place ℂ F) ℂ}
    (h : IsOriginalSheetFamily (jOver N ℂ) V ζ) (hV0 : (0 : ℂ) ∉ V) (hV1728 : (1728 : ℂ) ∉ V)
    (i : ι) : AnalyticCoord N := by
  have hc : ∀ P ∈ (ζ i).source,
      AnalyticAt ℂ (ζ i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
      deriv (ζ i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
    intro P hP
    obtain ⟨hreg, hval⟩ := h.2.1 i P hP
    have hvalV : originalPlaceEval N ℂ P (jOver N ℂ) ∈ V := by
      rw [← hval, ← h.1 i]
      exact (ζ i).map_source hP
    have hb0 : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 0 := fun hz => hV0 (hz ▸ hvalV)
    have hb1728 : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 1728 := fun hz => hV1728 (hz ▸ hvalV)
    have hne : jOver N ℂ - algebraMap ℂ F (originalPlaceEval N ℂ P (jOver N ℂ)) ≠ 0 := by
      intro hz
      exact transcendental_jOver N ℂ (sub_eq_zero.mp hz ▸ isAlgebraic_algebraMap _)
    have hpos := (OriginalChart.mem_originalPositiveFiber_iff_regular_eval N hne P).mpr ⟨hreg, rfl⟩
    have hord := original_finite_j_fiber_order_one N P _ hb0 hb1728
      ((mem_originalPositiveFiber N (jOver N ℂ) _ P).mp hpos)
    have heq : (ζ i ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) =ᶠ[𝓝 (0 : ℂ)]
        OriginalChart.chartRead N P (jOver N ℂ) := by
      have hsrc : ∀ᶠ z in 𝓝 (0 : ℂ), OriginalChart.placeFamily N P z ∈ (ζ i).source := by
        apply (OriginalChart.placeFamily_continuousAt_zero N P).preimage_mem_nhds
        rw [(OriginalChart.place_spec N P).2.1]
        exact (ζ i).open_source.mem_nhds hP
      filter_upwards [hsrc] with z hz
      change ζ i ((extChartAt 𝓘(ℂ, ℂ) P).symm z) =
        originalPlaceEval N ℂ (OriginalChart.placeFamily N P z) (jOver N ℂ)
      rw [OriginalChart.extPlaceChart_symm_apply]
      exact (h.2.1 i _ hz).2
    rw [OriginalChart.extPlaceChart_self]
    refine ⟨(OriginalChart.analyticAt_place_reading N P hreg).congr heq.symm, ?_⟩
    rw [heq.deriv_eq]
    exact OriginalChart.deriv_chartRead_ne_zero_of_order_one N P hreg hord
  exact ⟨ζ i, fun P hP => (hc P hP).1, fun P hP => (hc P hP).2⟩

theorem exists_original_j_analytic_sheet_neighborhood (b : ℂ) (hb0 : b ≠ 0) (hb1728 : b ≠ 1728) :
    ∃ (V : Set ℂ) (A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N),
      IsOpen V ∧ b ∈ V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
        IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ) := by
  obtain ⟨V, ζ, hV, hb, hz, h1728, hζ⟩ := exists_original_j_sheet_neighborhood N b hb0 hb1728
  exact ⟨V, hζ.analyticJCoord hz h1728, hV, hb, hz, h1728, hζ⟩

end
end Dubon2026.SourceFunctionField.CellGeometry

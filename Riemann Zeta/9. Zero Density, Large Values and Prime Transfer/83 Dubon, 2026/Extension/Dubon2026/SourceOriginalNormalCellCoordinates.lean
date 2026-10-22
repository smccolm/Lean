import Dubon2026.SourceOriginalPowerCoordinate
import Dubon2026.SourceOriginalChartTransitionDerivative
import Dubon2026.SourceOriginalAnalyticCellCoordinates

/-! DUB-17/18 -> geometric dissection -> branch-point cells.
The actual normal coordinates are analytic cell coordinates at every point
of their source, with the exact original evaluation power law. Recharting
uses the proved original manifold transitions, not an added hypothesis.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- A coordinate verified in one original chart is a genuine analytic cell coordinate. -/
def AnalyticCoord.ofOriginalChart (v : Place ℂ F)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hs : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (ha : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
      (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source))
    (hd : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) : AnalyticCoord N := by
  let G := ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm
  have heq : ∀ P ∈ ζ.source,
      (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) P P)]
        G ∘ (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) := by
    intro P hP
    have hm := MeromorphicCompact.eventually_symm_mem_source
      (x := v) (y := P) (mem_extChartAt_target P) (by rw [extChartAt_to_inv]; exact hs hP)
    filter_upwards [hm] with z hz
    simp only [G, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hz]
  have htrans : ∀ P ∈ ζ.source,
      AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm)
        (extChartAt 𝓘(ℂ, ℂ) P P) := by
    intro P hP
    exact OriginalChart.analyticAt_original_chart_transition v P (mem_extChartAt_target P)
      (by rw [extChartAt_to_inv]; exact hs hP)
  have hval : ∀ P : Place ℂ F,
      (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm)
        (extChartAt 𝓘(ℂ, ℂ) P P) = extChartAt 𝓘(ℂ, ℂ) v P := by
    intro P
    simp only [Function.comp_apply, extChartAt_to_inv]
  refine ⟨ζ, ?_, ?_⟩
  · intro P hP
    exact ((ha _ ⟨P, hP, rfl⟩).comp_of_eq (htrans P hP) (hval P)).congr (heq P hP).symm
  · intro P hP
    have hGa : AnalyticAt ℂ G
        ((extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm)
          (extChartAt 𝓘(ℂ, ℂ) P P)) := by
      rw [hval P]
      exact ha _ ⟨P, hP, rfl⟩
    rw [(heq P hP).deriv_eq, deriv_comp _ hGa.differentiableAt (htrans P hP).differentiableAt,
      hval P]
    exact mul_ne_zero (hd _ ⟨P, hP, rfl⟩)
      (OriginalChart.deriv_original_chart_transition_ne_zero v P (hs hP))

theorem exists_original_normal_cell_coordinate (v : Place ℂ F) {g : F}
    (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : originalPlaceEval N ℂ v g = 0) :
    ∃ (A : AnalyticCoord N) (ρ : ℝ), 0 < ρ ∧ v ∈ A.ζ.source ∧ A.ζ v = 0 ∧
      A.ζ.target = Metric.ball 0 ρ ∧ A.ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      0 < (v.ord g).toNat ∧ ∀ P ∈ A.ζ.source, g ∈ P.toValuationSubring ∧
        originalPlaceEval N ℂ P g = (A.ζ P) ^ (v.ord g).toNat := by
  obtain ⟨ζ, ρ, hρ, hv, hz, ht, hs, ha, hd, hgζ⟩ :=
    OriginalChart.exists_original_power_coordinate N v hne hg hg0
  refine ⟨AnalyticCoord.ofOriginalChart v ζ hs ha hd, ρ, hρ, hv, hz, ht, hs, ?_, hgζ⟩
  have ho := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v hg hne).mp hg0
  omega

end
end Dubon2026.SourceFunctionField.CellGeometry

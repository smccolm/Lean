import Dubon2026.SourceOriginalNormalCellCoordinates

/-! DUB-17/18 -> geometric cell dissection -> disjoint branch-point charts.
Shrink an actual analytic cell coordinate inside a prescribed neighborhood,
retaining its exact coordinate and inverse functions and a disk target.
This is the CompactShrink obligation in S_AlgebraicCurve_exists_dissectionScaleData,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The native restriction and target
neighborhood APIs avoid rebuilding the coordinate map.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
open scoped Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem AnalyticCoord.exists_disk_restriction (A : AnalyticCoord N) {v : Place ℂ F}
    (hv : v ∈ A.ζ.source) (hz : A.ζ v = 0) {U : Set (Place ℂ F)}
    (hU : IsOpen U) (hvU : v ∈ U) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (B : AnalyticCoord N) (r : ℝ), 0 < r ∧ r ≤ ρ ∧ v ∈ B.ζ.source ∧ B.ζ v = 0 ∧
      B.ζ.target = ball 0 r ∧ B.ζ.source ⊆ A.ζ.source ∧ B.ζ.source ⊆ U ∧
      (∀ P, B.ζ P = A.ζ P) ∧ ∀ z, B.ζ.symm z = A.ζ.symm z := by
  let H := A.ζ.restrOpen U hU
  have hvH : v ∈ H.source := ⟨hv, hvU⟩
  have hzH : H v = 0 := hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (H.open_target.mem_nhds (hzH ▸ H.map_source hvH))
  let r := min ε ρ
  have hr : 0 < r := lt_min hε hρ
  have hB : ball (0 : ℂ) r ⊆ H.target :=
    (ball_subset_ball (min_le_left ε ρ)).trans hεsub
  let ζ := H.trans (OpenPartialHomeomorph.ofSet (ball (0 : ℂ) r) isOpen_ball)
  let B : AnalyticCoord N :=
    { ζ := ζ
      analytic := fun P hP => A.analytic P hP.1.1
      deriv_ne := fun P hP => A.deriv_ne P hP.1.1 }
  refine ⟨B, r, hr, min_le_right _ _, ⟨hvH, ?_⟩, hz, ?_, ?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · change H v ∈ ball 0 r
    rw [hzH]
    exact mem_ball_self hr
  · change ball (0 : ℂ) r ∩ (OpenPartialHomeomorph.ofSet (ball (0 : ℂ) r)
      isOpen_ball).symm ⁻¹' H.target = ball 0 r
    rw [OpenPartialHomeomorph.ofSet_symm]
    exact inter_eq_left.mpr hB
  · exact fun _ hP => hP.1.1
  · exact fun _ hP => hP.1.2

end
end Dubon2026.SourceFunctionField.CellGeometry

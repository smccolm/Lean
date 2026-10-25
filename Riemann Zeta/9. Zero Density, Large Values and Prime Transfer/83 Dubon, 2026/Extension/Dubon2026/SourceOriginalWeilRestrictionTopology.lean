import Dubon2026.SourceOriginalWeilRestrictionComparison
import Dubon2026.SourceAnalyticRestrictionTopology

/-! DUB-17/18 -> auxiliary compactness -> actual restriction topology.
The proved normalized chart comparison and its nonzero derivative transport
the neighborhood filter exactly. Thus the literal place restriction is both
continuous and open; no continuity, openness or compactness input is supplied.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
local instance restrictionIntegral : Algebra.IsIntegral FF EE := Place.kummerIntegral n f
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem restriction_map_nhds (w : Place ℂ EE) :
    letI := placeTopology N n f D hf hfD
    letI := OriginalChart.placeTopology N
    Filter.map (fun w : Place ℂ EE => w.restrict FF) (𝓝 w) = 𝓝 (w.restrict FF) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  let e := (placeCore N n f D hf hfD).openPartialHomeomorph
    (placeChart N n f D hf hfD w) ⟨w, rfl⟩
  let d := (OriginalChart.placeCore N).openPartialHomeomorph
    (OriginalChart.placeChart N (w.restrict FF)) ⟨w.restrict FF, rfl⟩
  have he : e w = 0 := placeChart_self N n f D hf hfD w
  have hd : d (w.restrict FF) = 0 := OriginalChart.placeChart_self N (w.restrict FF)
  let g := (restrictionComparison N n f D hf hfD w).transition
  obtain ⟨ha, hderiv, hg0, hcomp⟩ := restriction_chart_comparison N n f D hf hfD w
  apply map_nhds_eq_of_analytic_chart_comparison (fun w : Place ℂ EE => w.restrict FF)
    e d (mem_placeChart_source N n f D hf hfD w)
    (OriginalChart.mem_placeChart_source N (w.restrict FF)) g (deriv g 0)
  · rw [he]
    exact ha.hasStrictDerivAt
  · exact hderiv
  · rw [he, hd]
    exact hg0
  · rw [he]
    exact hcomp

theorem continuous_restriction :
    letI := placeTopology N n f D hf hfD
    letI := OriginalChart.placeTopology N
    Continuous (fun w : Place ℂ EE => w.restrict FF) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  exact continuous_iff_continuousAt.mpr fun w => (restriction_map_nhds N n f D hf hfD w).le

theorem isOpenMap_restriction :
    letI := placeTopology N n f D hf hfD
    letI := OriginalChart.placeTopology N
    IsOpenMap (fun w : Place ℂ EE => w.restrict FF) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  exact isOpenMap_iff_nhds_le.mpr fun w => (restriction_map_nhds N n f D hf hfD w).ge

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

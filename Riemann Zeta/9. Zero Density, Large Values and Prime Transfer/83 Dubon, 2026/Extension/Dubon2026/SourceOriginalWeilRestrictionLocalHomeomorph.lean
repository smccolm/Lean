import Dubon2026.SourceOriginalWeilRestrictionTopology
import Dubon2026.SourceAnalyticCoveringComparison

/-! DUB-17/18 -> cover geometric reciprocity -> actual lifted cells.
The literal place restriction is a local homeomorphism, using the proved
unramified chart comparison, continuity and openness. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
attribute [local instance] restrictionIntegral
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem isLocalHomeomorph_restriction :
    letI := placeTopology N n f D hf hfD
    letI := OriginalChart.placeTopology N
    IsLocalHomeomorph (fun w : Place ℂ EE => w.restrict FF) := by
  letI := placeTopology N n f D hf hfD
  letI := OriginalChart.placeTopology N
  apply isLocalHomeomorph_of_continuous_open_locally_injective _
    (continuous_restriction N n f D hf hfD) (isOpenMap_restriction N n f D hf hfD)
  intro w
  let e := (placeCore N n f D hf hfD).openPartialHomeomorph
    (placeChart N n f D hf hfD w) ⟨w, rfl⟩
  let d := (OriginalChart.placeCore N).openPartialHomeomorph
    (OriginalChart.placeChart N (w.restrict FF)) ⟨w.restrict FF, rfl⟩
  have he : e w = 0 := placeChart_self N n f D hf hfD w
  have hd : d (w.restrict FF) = 0 := OriginalChart.placeChart_self N (w.restrict FF)
  let g := (restrictionComparison N n f D hf hfD w).transition
  obtain ⟨ha, hderiv, hg0, hcomp⟩ := restriction_chart_comparison N n f D hf hfD w
  apply exists_nhds_injOn_of_analytic_chart_comparison (fun w : Place ℂ EE => w.restrict FF)
    e d (mem_placeChart_source N n f D hf hfD w)
    (OriginalChart.mem_placeChart_source N (w.restrict FF)) g (deriv g 0)
  · rw [he]
    exact ha.hasStrictDerivAt
  · exact hderiv
  · rw [he, hd]
    exact hg0
  · rw [he]
    exact hcomp

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

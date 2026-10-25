import Dubon2026.SourceCurveUnramifiedChartRestriction
import Dubon2026.SourceCurveAnalyticChartBranchEquality
import Dubon2026.SourceOriginalWeilCoverChartOrders
import Dubon2026.SourceOriginalWeilEveryLocalCover
import Dubon2026.SourceOriginalNormEvaluation

/-! DUB-17/18 -> auxiliary compactness -> the actual restriction map.
The existing original curve charts and the constructed Kummer cover charts
have the same normalized orders under restriction. Uniformizer comparison
therefore identifies their actual branches locally, with nonzero derivative.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem restriction_family_orders (w : Place ℂ EE) :
    AnalyticChart.Orders (original_place_residue_algebraMap_bijective N ℂ)
      (fun z => (placeFamily N n f D hf hfD w z).restrict FF)
      (Metric.ball 0 (placeRadius N n f D hf hfD w)) :=
  AnalyticChart.Orders.restrict_unramified
    (original_place_residue_algebraMap_bijective N ℂ)
    (originalWeilKummerCover_residue_bijective N ℂ n f)
    (OriginalChart.originalWeil_complex_kummer_unramified N n f D hf hfD)
    (place_spec N n f D hf hfD w).2.2.1

/-- The actual cover-to-base chart comparison, with its order inputs discharged. -/
def restrictionComparison (w : Place ℂ EE) :
    AnalyticChart.ComparisonData (original_place_residue_algebraMap_bijective N ℂ) where
  γ := OriginalChart.placeFamily N (w.restrict FF)
  γ' := fun z => (placeFamily N n f D hf hfD w z).restrict FF
  v := w.restrict FF
  U := Metric.ball 0 (OriginalChart.placeRadius N (w.restrict FF))
  U' := Metric.ball 0 (placeRadius N n f D hf hfD w)
  z₀ := 0
  z₀' := 0
  hU := Metric.ball_mem_nhds 0 (OriginalChart.place_spec N (w.restrict FF)).1
  hU' := Metric.ball_mem_nhds 0 (place_spec N n f D hf hfD w).1
  h₀ := by rw [(place_spec N n f D hf hfD w).2.1,
    (OriginalChart.place_spec N (w.restrict FF)).2.1]
  ht := (OriginalChart.place_spec N (w.restrict FF)).2.2.2
  hγ := (OriginalChart.place_spec N (w.restrict FF)).2.2.1
  hγ' := restriction_family_orders N n f D hf hfD w

theorem restriction_chart_comparison (w : Place ℂ EE) :
    let g := (restrictionComparison N n f D hf hfD w).transition
    AnalyticAt ℂ g 0 ∧ deriv g 0 ≠ 0 ∧ g 0 = 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), (placeFamily N n f D hf hfD w z).restrict FF =
        OriginalChart.placeFamily N (w.restrict FF) (g z) := by
  let S := restrictionComparison N n f D hf hfD w
  exact ⟨S.analyticAt_transition, S.deriv_transition_ne_zero,
    S.transition_self, S.eventually_place_eq⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

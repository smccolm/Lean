import Dubon2026.SourceOriginalWeilCoverChartOrders
import Dubon2026.SourceCurveAnalyticChartOrders

/-! DUB-17/18 -> auxiliary connectedness -> actual residue continuity.
At a regular place the constructed chart reading is analytic. Composing
with the native chart gives continuity of the genuine cover residue value.
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

theorem analyticAt_place_reading (v : Place ℂ EE) {a : EE}
    (ha : a ∈ v.toValuationSubring) :
    AnalyticAt ℂ (fun z => (placeFamily N n f D hf hfD v z).rationalEval
      (originalWeilKummerCover_residue_bijective N ℂ n f _) a) 0 := by
  apply (place_spec N n f D hf hfD v).2.2.1.analyticAt
    (Metric.mem_ball_self (place_spec N n f D hf hfD v).1)
  simpa only [(place_spec N n f D hf hfD v).2.1] using ha

theorem placeFamily_continuousAt_zero (v : Place ℂ EE) :
    letI := placeTopology N n f D hf hfD
    ContinuousAt (placeFamily N n f D hf hfD v) 0 := by
  letI := placeTopology N n f D hf hfD
  exact (continuousOn_placeFamily N n f D hf hfD v).continuousAt
    (Metric.ball_mem_nhds 0 (place_spec N n f D hf hfD v).1)

theorem continuousAt_place_eval (v : Place ℂ EE) {a : EE}
    (ha : a ∈ v.toValuationSubring) :
    letI := placeTopology N n f D hf hfD
    ContinuousAt (fun w => w.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f w) a) v := by
  letI := placeTopology N n f D hf hfD
  let e := (placeCore N n f D hf hfD).openPartialHomeomorph
    (placeChart N n f D hf hfD v) ⟨v, rfl⟩
  have hc : ContinuousAt (placeChart N n f D hf hfD v) v :=
    e.continuousAt (mem_placeChart_source N n f D hf hfD v)
  have han : ContinuousAt (fun z => (placeFamily N n f D hf hfD v z).rationalEval
      (originalWeilKummerCover_residue_bijective N ℂ n f _) a)
      (placeChart N n f D hf hfD v v) := by
    rw [placeChart_self]
    exact (analyticAt_place_reading N n f D hf hfD v ha).continuousAt
  apply (han.comp hc).congr
  filter_upwards [e.open_source.mem_nhds (mem_placeChart_source N n f D hf hfD v)] with w hw
  exact congrArg (fun P => P.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f P) a)
    ((placeChart N n f D hf hfD v).left_inv hw)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

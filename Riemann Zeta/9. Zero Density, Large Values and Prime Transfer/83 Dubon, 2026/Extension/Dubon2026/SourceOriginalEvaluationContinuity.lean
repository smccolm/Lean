import Dubon2026.SourceOriginalChartFiberData

/-! DUB-17/18 -> original torsion cardinality -> connected complex curve.
An original function regular at a place has continuous literal residue
evaluation there. Its already proved analytic reading in the uniformizer
chart composes with the native continuous chart; the exact inverse law
identifies this composition with the original evaluation near the place.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem continuousAt_originalPlaceEval (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {f : modularFunctionFieldOver N ℂ} (hf : f ∈ v.toValuationSubring) :
    letI := placeTopology N
    ContinuousAt (fun w => originalPlaceEval N ℂ w f) v := by
  letI := placeTopology N
  let e := (placeCore N).openPartialHomeomorph (placeChart N v) ⟨v, rfl⟩
  have hc : ContinuousAt (placeChart N v) v := e.continuousAt (mem_placeChart_source N v)
  have ha : ContinuousAt (fun z => originalPlaceEval N ℂ (placeFamily N v z) f)
      (placeChart N v v) := by
    rw [placeChart_self]
    exact (analyticAt_place_reading N v hf).continuousAt
  apply (ha.comp hc).congr
  filter_upwards [e.open_source.mem_nhds (mem_placeChart_source N v)] with w hw
  exact congrArg (fun P => originalPlaceEval N ℂ P f) ((placeChart N v).left_inv hw)

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalChartFiberOrders

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> weighted fiber contour. Restate exact chart multiplicity
at a place using the already proved inverse law of its original chart.
This is the literal multiplicity needed to reindex the divisor sum.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_chart_order_at_place (v w : Place ℂ F)
    (hw : w ∈ (placeChart N v).source) {f : F} (hf : f ∈ w.toValuationSubring)
    (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    analyticOrderAt (fun z => chartRead N v f z - t) (placeChart N v w) ≠ ⊤ ∧
      w.ord (f - algebraMap ℂ F t) =
        (analyticOrderNatAt (fun z => chartRead N v f z - t) (placeChart N v w) : ℤ) := by
  have hs : placeFamily N v (placeChart N v w) = w := (placeChart N v).left_inv hw
  have hf' : f ∈ (placeFamily N v (placeChart N v w)).toValuationSubring := by rwa [hs]
  have ho := chartRead_order_sub N v ((placeChart N v).map_source hw) hf' t hne
  rwa [hs] at ho

end
end Dubon2026.SourceFunctionField.OriginalChart

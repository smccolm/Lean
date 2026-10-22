import Dubon2026.SourceOriginalChartDifferentials

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> analytic fiber multiplicities and simple nearby fibers.
The proved original chart order property holds at every point of a chart,
so it identifies analytic multiplicity directly, without rebuilding chart
transitions. Native analytic derivative order gives nonvanishing off the
center for every nonconstant original function regular at that center.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem chartRead_order_sub (v : Place ℂ F) {z : ℂ}
    (hz : z ∈ ball 0 (placeRadius N v)) {f : F}
    (hf : f ∈ (placeFamily N v z).toValuationSubring) (t : ℂ)
    (hne : f - algebraMap ℂ F t ≠ 0) :
    analyticOrderAt (fun u => chartRead N v f u - t) z ≠ ⊤ ∧
      (placeFamily N v z).ord (f - algebraMap ℂ F t) =
        (analyticOrderNatAt (fun u => chartRead N v f u - t) z : ℤ) := by
  have ha : AnalyticAt ℂ (fun u => chartRead N v f u - t) z :=
    ((place_spec N v).2.2.1.analyticAt hz hf).sub analyticAt_const
  have ho := (place_spec N v).2.2.1.meromorphicOrderAt_sub_const
    (isOpen_ball.mem_nhds hz) hf t hne
  change meromorphicOrderAt (fun u => chartRead N v f u - t) z = _ at ho
  rw [ha.meromorphicOrderAt_eq] at ho
  simp only [analyticOrderNatAt]
  generalize analyticOrderAt (fun u => chartRead N v f u - t) z = o at ho ⊢
  change o ≠ ⊤ ∧ _ = (o.toNat : ℤ)
  induction o using ENat.recTopCoe with
  | top => simp at ho
  | coe m =>
    simp only [ENat.map_coe, WithTop.coe_eq_coe] at ho
    exact ⟨ENat.coe_ne_top m, by simpa using ho.symm⟩

theorem eventually_deriv_chartRead_ne_zero (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring) (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (chartRead N v f) z ≠ 0 := by
  have ha : AnalyticAt ℂ (chartRead N v f) 0 := analyticAt_place_reading N v hf
  have hm : f ∈ (placeFamily N v 0).toValuationSubring := by
    rwa [(place_spec N v).2.1]
  have ho := (chartRead_order_sub N v (mem_ball_self (place_spec N v).1) hm
    (chartRead N v f 0) (fun h => hfc _ (sub_eq_zero.mp h))).1
  rcases ha.deriv.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · have hd := ha.analyticOrderAt_deriv_add_one
    rw [analyticOrderAt_eq_top.mpr h0, top_add] at hd
    exact False.elim (ho hd.symm)
  · exact h1

end
end Dubon2026.SourceFunctionField.OriginalChart

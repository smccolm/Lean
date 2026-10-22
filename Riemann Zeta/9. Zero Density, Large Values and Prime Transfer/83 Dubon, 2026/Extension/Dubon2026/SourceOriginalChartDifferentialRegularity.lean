import Dubon2026.SourceOriginalChartDifferentials
import Dubon2026.SourceOriginalRegularOrders
import Dubon2026.SourceOriginalExactDerivativeOrder

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> compatible
path primitives. An actual chart uniformizer has order-one differences
throughout its disk. The already proved exact derivative-order theorem
therefore makes its differential a unit at every point. Every original
regular differential has a regular coefficient and analytic reading on
the whole chart disk, not only at its center.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem chart_dCoord_order_zero (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    (placeFamily N v z).ordDifferential v.dCoord = 0 := by
  have ho := (place_spec N v).2.2.2 z hz
  have h := original_ordDifferential_D_eq_ord_sub_one N ℂ (placeFamily N v z)
    (f := v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z)
    (by rw [ho]; exact one_ne_zero)
  rw [map_sub, Derivation.map_algebraMap, sub_zero, ho, sub_self] at h
  exact h

theorem chart_differentialCoeff_regular (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    v.differentialCoeff ω ∈ (placeFamily N v z).toValuationSubring := by
  haveI := original_place_dCoordGenerates N ℂ v
  haveI := original_place_dCoordGenerates N ℂ (placeFamily N v z)
  haveI : Nontrivial Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  by_cases hc : v.differentialCoeff ω = 0
  · rw [hc]
    exact zero_mem _
  have hd : (placeFamily N v z).differentialCoeff v.dCoord ≠ 0 := by
    intro he
    have h := (placeFamily N v z).differentialCoeff_smul_dCoord v.dCoord
    rw [he, zero_smul] at h
    exact (original_place_dCoord_ne_zero N ℂ v) h.symm
  have hs := (placeFamily N v z).ordDifferential_smul hc hd
  rw [v.differentialCoeff_smul_dCoord ω, chart_dCoord_order_zero N v hz, add_zero] at hs
  have hr := (mem_original_regularDifferentials_iff_ord_nonneg N ℂ ω).mp hω (placeFamily N v z)
  rw [hs] at hr
  exact (placeFamily N v z).mem_of_ord_nonneg hr

theorem analyticOnNhd_readDifferential (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    AnalyticOnNhd ℂ (readDifferential N v ω) (ball 0 (placeRadius N v)) := by
  intro z hz
  have ha : AnalyticAt ℂ (chartRead N v (v.differentialCoeff ω)) z :=
    (place_spec N v).2.2.1.analyticAt hz (chart_differentialCoeff_regular N v ω hω hz)
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact (readDifferential_eq_coefficient N v ω hu).symm

end
end Dubon2026.SourceFunctionField.OriginalChart

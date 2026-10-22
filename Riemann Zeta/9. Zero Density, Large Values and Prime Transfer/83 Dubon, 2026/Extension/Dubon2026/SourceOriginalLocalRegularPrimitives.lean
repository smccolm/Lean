import Dubon2026.SourceOriginalDifferentialTransitions
import Dubon2026.SourceOriginalChartPrimitives

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
period correction and meromorphic exponential -> primitives along paths
avoiding poles. Only regularity at the indicated original place is needed
for a local primitive. The existing punctured differential-germ identity
and exact chart orders supply the transition law at any regular overlap.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem analyticAt_readDifferential_of_coeff_mem (v : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : v.differentialCoeff ω ∈ v.toValuationSubring) :
    AnalyticAt ℂ (readDifferential N v ω) 0 := by
  have ha := analyticAt_place_reading N v hω
  apply ha.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N v).1] with z hz
  exact (readDifferential_eq_coefficient N v ω hz).symm

theorem exists_readDifferential_local_primitive (v : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : v.differentialCoeff ω ∈ v.toValuationSubring) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N v ∧ ∃ Φ : ℂ → ℂ,
      ∀ z ∈ ball (0 : ℂ) r, HasDerivAt Φ (readDifferential N v ω z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((analyticAt_readDifferential_of_coeff_mem N v ω hω).eventually_analyticAt.and
      (ball_mem_nhds (0 : ℂ) (place_spec N v).1))
  let r' := min r (placeRadius N v) / 2
  have hr' : 0 < r' := half_pos (lt_min hr (place_spec N v).1)
  have hsub : ball (0 : ℂ) r' ⊆ ball 0 r :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr (place_spec N v).1))).trans (min_le_left _ _))
  refine ⟨r', hr', (half_lt_self (lt_min hr (place_spec N v).1)).trans_le (min_le_right _ _), ?_⟩
  have hd : DifferentiableOn ℂ (readDifferential N v ω) (ball 0 r') :=
    fun z hz => (hball (hsub hz)).1.differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball

theorem chart_differentialCoeff_regular_at (v w : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : w.differentialCoeff ω ∈ w.toValuationSubring)
    (hw : w ∈ (placeChart N v).source) : v.differentialCoeff ω ∈ w.toValuationSubring := by
  obtain ⟨z, hz, rfl⟩ := hw
  haveI := original_place_dCoordGenerates N ℂ v
  haveI := original_place_dCoordGenerates N ℂ (placeFamily N v z)
  haveI : Nontrivial Ω[F⁄ℂ] :=
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
  have hr : 0 ≤ (placeFamily N v z).ordDifferential ω :=
    (placeFamily N v z).ord_nonneg_of_mem hω
  rw [hs] at hr
  exact (placeFamily N v z).mem_of_ord_nonneg hr

theorem readDifferential_change_of_coeff_mem (v w : Place ℂ F) (ω : Ω[F⁄ℂ])
    (hω : w.differentialCoeff ω ∈ w.toValuationSubring)
    (hw : w ∈ (placeChart N v).source) :
    readDifferential N w ω =ᶠ[𝓝 (0 : ℂ)] fun z =>
      readDifferential N v ω (chartRead N w v.uniformizer z) *
        deriv (chartRead N w v.uniformizer) z := by
  letI := placeTopology N
  haveI := original_place_dCoordGenerates N ℂ v
  have hh := chart_differentialCoeff_regular_at N v w ω hω hw
  have hg := uniformizer_regular_on_chart N v w hw
  have ha := analyticAt_place_reading N w hh
  have hb := analyticAt_place_reading N w hg
  have he : readDifferential N w ω =ᶠ[𝓝 (0 : ℂ)]
      chartRead N w (v.differentialCoeff ω) * deriv (chartRead N w v.uniformizer) :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (analyticAt_readDifferential_of_coeff_mem N w ω hω).continuousAt
      (ha.continuousAt.mul hb.deriv.continuousAt)).mp
        (readDifferential_eq_expression_germ N w ω (v.differentialCoeff ω) v.uniformizer
          (v.differentialCoeff_smul_dCoord ω).symm)
  have hc := placeFamily_continuousAt_zero N w
  rw [ContinuousAt, (place_spec N w).2.1] at hc
  have hs : ∀ᶠ z in 𝓝 (0 : ℂ), placeFamily N w z ∈ (placeChart N v).source :=
    hc.eventually (((placeCore N).openPartialHomeomorph (placeChart N v)
      ⟨v, rfl⟩).open_source.mem_nhds hw)
  filter_upwards [he, hs] with z hz hzs
  have ht : chartRead N w v.uniformizer z ∈ ball 0 (placeRadius N v) :=
    (placeChart N v).map_source hzs
  have hi : placeFamily N v (chartRead N w v.uniformizer z) = placeFamily N w z :=
    (placeChart N v).left_inv hzs
  rw [hz, readDifferential_eq_coefficient N v ω ht]
  change chartRead N w (v.differentialCoeff ω) z * _ =
    originalPlaceEval N ℂ (placeFamily N v (chartRead N w v.uniformizer z))
      (v.differentialCoeff ω) * _
  rw [hi]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalChart

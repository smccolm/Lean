import Dubon2026.SourceOriginalWeilCoverDifferentialTransitions
import Dubon2026.SourceOriginalWeilCoverChartPrimitives

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem analyticAt_readDifferential_of_coeff_mem (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : v.differentialCoeff ω ∈ v.toValuationSubring) :
    AnalyticAt ℂ (readDifferential N n radicand A hRadicand hOrders v ω) 0 := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have ha := analyticAt_place_reading N n radicand A hRadicand hOrders v hω
  apply ha.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N n radicand A hRadicand hOrders v).1] with z hz
  exact (readDifferential_eq_coefficient N n radicand A hRadicand hOrders v ω hz).symm

theorem exists_readDifferential_local_primitive (v : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : v.differentialCoeff ω ∈ v.toValuationSubring) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N n radicand A hRadicand hOrders v ∧ ∃ Φ : ℂ → ℂ,
      ∀ z ∈ ball (0 : ℂ) r, HasDerivAt Φ (readDifferential N n radicand A hRadicand hOrders v ω z) z := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((analyticAt_readDifferential_of_coeff_mem N n radicand A hRadicand hOrders v ω hω).eventually_analyticAt.and
      (ball_mem_nhds (0 : ℂ) (place_spec N n radicand A hRadicand hOrders v).1))
  let r' := min r (placeRadius N n radicand A hRadicand hOrders v) / 2
  have hr' : 0 < r' := half_pos (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1)
  have hsub : ball (0 : ℂ) r' ⊆ ball 0 r :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1))).trans (min_le_left _ _))
  refine ⟨r', hr', (half_lt_self (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1)).trans_le (min_le_right _ _), ?_⟩
  have hd : DifferentiableOn ℂ (readDifferential N n radicand A hRadicand hOrders v ω) (ball 0 r') :=
    fun z hz => (hball (hsub hz)).1.differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball

theorem chart_differentialCoeff_regular_at (v w : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : w.differentialCoeff ω ∈ w.toValuationSubring)
    (hw : w ∈ (placeChart N n radicand A hRadicand hOrders v).source) : v.differentialCoeff ω ∈ w.toValuationSubring := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨z, hz, rfl⟩ := hw
  haveI := cover_place_dCoordGenerates N n radicand v
  haveI := cover_place_dCoordGenerates N n radicand (placeFamily N n radicand A hRadicand hOrders v z)
  haveI := cover_differentials_nontrivial N n radicand
  by_cases hc : v.differentialCoeff ω = 0
  · rw [hc]
    exact zero_mem _
  have hd : (placeFamily N n radicand A hRadicand hOrders v z).differentialCoeff v.dCoord ≠ 0 := by
    intro he
    have h := (placeFamily N n radicand A hRadicand hOrders v z).differentialCoeff_smul_dCoord v.dCoord
    rw [he, zero_smul] at h
    exact v.dCoord_ne_zero h.symm
  have hs := (placeFamily N n radicand A hRadicand hOrders v z).ordDifferential_smul hc hd
  rw [v.differentialCoeff_smul_dCoord ω, chart_dCoord_order_zero N n radicand A hRadicand hOrders v hz, add_zero] at hs
  have hr : 0 ≤ (placeFamily N n radicand A hRadicand hOrders v z).ordDifferential ω :=
    (placeFamily N n radicand A hRadicand hOrders v z).ord_nonneg_of_mem hω
  rw [hs] at hr
  exact (placeFamily N n radicand A hRadicand hOrders v z).mem_of_ord_nonneg hr

theorem readDifferential_change_of_coeff_mem (v w : Place ℂ EE) (ω : Ω[EE⁄ℂ])
    (hω : w.differentialCoeff ω ∈ w.toValuationSubring)
    (hw : w ∈ (placeChart N n radicand A hRadicand hOrders v).source) :
    readDifferential N n radicand A hRadicand hOrders w ω =ᶠ[𝓝 (0 : ℂ)] fun z =>
      readDifferential N n radicand A hRadicand hOrders v ω (chartRead N n radicand A hRadicand hOrders w v.uniformizer z) *
        deriv (chartRead N n radicand A hRadicand hOrders w v.uniformizer) z := by
  letI := placeTopology N n radicand A hRadicand hOrders
  haveI := cover_place_dCoordGenerates N n radicand v
  have hh := chart_differentialCoeff_regular_at N n radicand A hRadicand hOrders v w ω hω hw
  have hg := uniformizer_regular_on_chart N n radicand A hRadicand hOrders v w hw
  have ha := analyticAt_place_reading N n radicand A hRadicand hOrders w hh
  have hb := analyticAt_place_reading N n radicand A hRadicand hOrders w hg
  have he : readDifferential N n radicand A hRadicand hOrders w ω =ᶠ[𝓝 (0 : ℂ)]
      chartRead N n radicand A hRadicand hOrders w (v.differentialCoeff ω) * deriv (chartRead N n radicand A hRadicand hOrders w v.uniformizer) :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (analyticAt_readDifferential_of_coeff_mem N n radicand A hRadicand hOrders w ω hω).continuousAt
      (ha.continuousAt.mul hb.deriv.continuousAt)).mp
        (readDifferential_eq_expression_germ N n radicand A hRadicand hOrders w ω (v.differentialCoeff ω) v.uniformizer
          (v.differentialCoeff_smul_dCoord ω).symm)
  have hc := placeFamily_continuousAt_zero N n radicand A hRadicand hOrders w
  rw [ContinuousAt, (place_spec N n radicand A hRadicand hOrders w).2.1] at hc
  have hs : ∀ᶠ z in 𝓝 (0 : ℂ), placeFamily N n radicand A hRadicand hOrders w z ∈ (placeChart N n radicand A hRadicand hOrders v).source :=
    hc.eventually (((placeCore N n radicand A hRadicand hOrders).openPartialHomeomorph (placeChart N n radicand A hRadicand hOrders v)
      ⟨v, rfl⟩).open_source.mem_nhds hw)
  filter_upwards [he, hs] with z hz hzs
  have ht : chartRead N n radicand A hRadicand hOrders w v.uniformizer z ∈ ball 0 (placeRadius N n radicand A hRadicand hOrders v) :=
    (placeChart N n radicand A hRadicand hOrders v).map_source hzs
  have hi : placeFamily N n radicand A hRadicand hOrders v (chartRead N n radicand A hRadicand hOrders w v.uniformizer z) = placeFamily N n radicand A hRadicand hOrders w z :=
    (placeChart N n radicand A hRadicand hOrders v).left_inv hzs
  rw [hz, readDifferential_eq_coefficient N n radicand A hRadicand hOrders v ω ht]
  change chartRead N n radicand A hRadicand hOrders w (v.differentialCoeff ω) z * _ =
    (placeFamily N n radicand A hRadicand hOrders v (chartRead N n radicand A hRadicand hOrders w v.uniformizer z)).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand _)
      (v.differentialCoeff ω) * _
  rw [hi]
  rfl


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

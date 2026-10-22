import Dubon2026.SourceOriginalChartGermDerivation
import Dubon2026.SourceOriginalChartDifferentialRegularity
import Dubon2026.SourceOriginalFiberOrderSupport

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> path periods.
The actual differential readings satisfy the coordinate-change law on
overlapping original place charts. The Kaehler universal-map identity
supplies the derivative comparison; proved regularity extends the
punctured identity across the center. This discharges compatibility
needed to glue local primitives along actual continuous paths.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem uniformizer_regular_on_chart (v w : Place ℂ (modularFunctionFieldOver N ℂ))
    (hw : w ∈ (placeChart N v).source) : v.uniformizer ∈ w.toValuationSubring := by
  obtain ⟨y, hy, rfl⟩ := hw
  apply (original_sub_const_mem_iff N (placeFamily N v y) v.uniformizer y).mp
  apply (placeFamily N v y).mem_of_ord_nonneg
  rw [(place_spec N v).2.2.2 y hy]
  exact zero_le_one

theorem readDifferential_eq_expression_nhds
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (h g : modularFunctionFieldOver N ℂ)
    (hh : h ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring)
    (he : ω = h • D ℂ (modularFunctionFieldOver N ℂ) g) :
    readDifferential N v ω =ᶠ[𝓝 (0 : ℂ)]
      chartRead N v h * deriv (chartRead N v g) := by
  have ha : AnalyticAt ℂ (chartRead N v h) 0 := analyticAt_place_reading N v hh
  have hb : AnalyticAt ℂ (chartRead N v g) 0 := analyticAt_place_reading N v hg
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (analyticAt_readDifferential N v ω hω).continuousAt
      (ha.continuousAt.mul hb.deriv.continuousAt)).mp
        (readDifferential_eq_expression_germ N v ω h g he)

theorem readDifferential_change (v w : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (hw : w ∈ (placeChart N v).source) :
    readDifferential N w ω =ᶠ[𝓝 (0 : ℂ)] fun z =>
      readDifferential N v ω (chartRead N w v.uniformizer z) *
        deriv (chartRead N w v.uniformizer) z := by
  letI := placeTopology N
  haveI := original_place_dCoordGenerates N ℂ v
  have hh : v.differentialCoeff ω ∈ w.toValuationSubring := by
    obtain ⟨y, hy, rfl⟩ := hw
    exact chart_differentialCoeff_regular N v ω hω hy
  have he := readDifferential_eq_expression_nhds N w ω hω (v.differentialCoeff ω)
    v.uniformizer hh (uniformizer_regular_on_chart N v w hw)
      (v.differentialCoeff_smul_dCoord ω).symm
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

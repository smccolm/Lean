import Dubon2026.SourceOriginalWeilCoverChartGermDerivation
import Dubon2026.SourceOriginalWeilCoverDifferentialRegularity

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel comparison.
Adapt the proved original-curve coordinate and primitive arguments to the
literal Kummer cover, using its constructed charts and finite coordinate.
The primitive gluing argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem uniformizer_regular_on_chart (v w : Place ℂ (EE))
    (hw : w ∈ (placeChart N n r A hr hrA v).source) : v.uniformizer ∈ w.toValuationSubring := by
  obtain ⟨y, hy, rfl⟩ := hw
  have hm : v.uniformizer - algebraMap ℂ EE y ∈
      (placeFamily N n r A hr hrA v y).toValuationSubring := by
    apply (placeFamily N n r A hr hrA v y).mem_of_ord_nonneg
    rw [(place_spec N n r A hr hrA v).2.2.2 y hy]
    exact zero_le_one
  simpa only [sub_add_cancel] using
    add_mem hm ((placeFamily N n r A hr hrA v y).algebraMap_mem' y)

theorem readDifferential_eq_expression_nhds
    (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    (h g : EE)
    (hh : h ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring)
    (he : ω = h • D ℂ (EE) g) :
    readDifferential N n r A hr hrA v ω =ᶠ[𝓝 (0 : ℂ)]
      chartRead N n r A hr hrA v h * deriv (chartRead N n r A hr hrA v g) := by
  have ha : AnalyticAt ℂ (chartRead N n r A hr hrA v h) 0 := analyticAt_place_reading N n r A hr hrA v hh
  have hb : AnalyticAt ℂ (chartRead N n r A hr hrA v g) 0 := analyticAt_place_reading N n r A hr hrA v hg
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (analyticAt_readDifferential N n r A hr hrA v ω hω).continuousAt
      (ha.continuousAt.mul hb.deriv.continuousAt)).mp
        (readDifferential_eq_expression_germ N n r A hr hrA v ω h g he)

theorem readDifferential_change (v w : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    (hw : w ∈ (placeChart N n r A hr hrA v).source) :
    readDifferential N n r A hr hrA w ω =ᶠ[𝓝 (0 : ℂ)] fun z =>
      readDifferential N n r A hr hrA v ω (chartRead N n r A hr hrA w v.uniformizer z) *
        deriv (chartRead N n r A hr hrA w v.uniformizer) z := by
  letI := placeTopology N n r A hr hrA
  haveI := cover_place_dCoordGenerates N n r v
  have hh : v.differentialCoeff ω ∈ w.toValuationSubring := by
    obtain ⟨y, hy, rfl⟩ := hw
    exact chart_differentialCoeff_regular N n r A hr hrA v ω hω hy
  have he := readDifferential_eq_expression_nhds N n r A hr hrA w ω hω (v.differentialCoeff ω)
    v.uniformizer hh (uniformizer_regular_on_chart N n r A hr hrA v w hw)
      (v.differentialCoeff_smul_dCoord ω).symm
  have hc := placeFamily_continuousAt_zero N n r A hr hrA w
  rw [ContinuousAt, (place_spec N n r A hr hrA w).2.1] at hc
  have hs : ∀ᶠ z in 𝓝 (0 : ℂ), placeFamily N n r A hr hrA w z ∈ (placeChart N n r A hr hrA v).source :=
    hc.eventually (((placeCore N n r A hr hrA).openPartialHomeomorph (placeChart N n r A hr hrA v)
      ⟨v, rfl⟩).open_source.mem_nhds hw)
  filter_upwards [he, hs] with z hz hzs
  have ht : chartRead N n r A hr hrA w v.uniformizer z ∈ ball 0 (placeRadius N n r A hr hrA v) :=
    (placeChart N n r A hr hrA v).map_source hzs
  have hi : placeFamily N n r A hr hrA v (chartRead N n r A hr hrA w v.uniformizer z) = placeFamily N n r A hr hrA w z :=
    (placeChart N n r A hr hrA v).left_inv hzs
  rw [hz, readDifferential_eq_coefficient N n r A hr hrA v ω ht]
  change chartRead N n r A hr hrA w (v.differentialCoeff ω) z * _ =
    (placeFamily N n r A hr hrA v (chartRead N n r A hr hrA w v.uniformizer z)).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r _)
      (v.differentialCoeff ω) * _
  rw [hi]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

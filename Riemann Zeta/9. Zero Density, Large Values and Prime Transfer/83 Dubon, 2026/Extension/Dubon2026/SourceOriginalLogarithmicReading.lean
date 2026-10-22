import Dubon2026.SourceOriginalSimplePoleRegularPart
import Dubon2026.SourceOriginalLocalRegularPrimitives

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic exponential. In its actual original uniformizer chart a simple
pole reading is its residue divided by z plus an analytic coefficient.
The exact coordinate identity eliminates the external auxiliary coordinate
factor, so a native primitive of the regular part supplies the local model.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_logarithmic_reading (v : Place ℂ F) (η : Ω[F⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = c) :
    ∃ b : F, b ∈ v.toValuationSubring ∧
      readDifferential N v η =ᶠ[𝓝[≠] (0 : ℂ)] fun z => c * z⁻¹ + chartRead N v b z := by
  let b := v.differentialCoeff η - algebraMap ℂ F c * v.uniformizer⁻¹
  refine ⟨b, original_simple_pole_regular_part N v η hη c hc, ?_⟩
  have hs : v.differentialCoeff η = algebraMap ℂ F c * v.uniformizer⁻¹ + b := by
    dsimp [b]
    ring
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N v) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (place_spec N v).1)
  filter_upwards [hb, chartRead_add N v (algebraMap ℂ F c * v.uniformizer⁻¹) b,
    chartRead_mul N v (algebraMap ℂ F c) v.uniformizer⁻¹,
    chartRead_inv N v v.uniformizer_ne_zero] with z hz ha hm hi
  rw [readDifferential_eq_coefficient N v η hz, hs, ha, Pi.add_apply,
    hm, Pi.mul_apply, hi, Pi.inv_apply, chartRead_algebraMap, chartRead_uniformizer N v hz]

theorem exists_original_logarithmic_primitive (v : Place ℂ F) (η : Ω[F⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = c) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N v ∧ ∃ Ψ : ℂ → ℂ,
      AnalyticAt ℂ Ψ 0 ∧ ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
        HasDerivAt Ψ (readDifferential N v η z - c * z⁻¹) z := by
  obtain ⟨b, hb, hread⟩ := exists_original_logarithmic_reading N v η hη c hc
  have ha := analyticAt_place_reading N v hb
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hread
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (ha.eventually_analyticAt.and hread)
  let r' := min r (placeRadius N v) / 2
  have hr' : 0 < r' := half_pos (lt_min hr (place_spec N v).1)
  have hsub : ball (0 : ℂ) r' ⊆ ball 0 r :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr (place_spec N v).1))).trans (min_le_left _ _))
  have hd : DifferentiableOn ℂ (chartRead N v b) (ball 0 r') :=
    fun z hz => (hball z (hsub hz)).1.differentiableAt.differentiableWithinAt
  obtain ⟨Ψ, hΨ⟩ := hd.isExactOn_ball
  refine ⟨r', hr', (half_lt_self (lt_min hr (place_spec N v).1)).trans_le (min_le_right _ _),
    Ψ, ?_, fun z hz hn => ?_⟩
  · exact DifferentiableOn.analyticAt
      (fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt) (ball_mem_nhds 0 hr')
  · have he := (hball z (hsub hz)).2 hn
    rw [he, add_sub_cancel_left]
    exact hΨ z hz

end
end Dubon2026.SourceFunctionField.OriginalChart

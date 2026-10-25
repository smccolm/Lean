import Dubon2026.SourceOriginalWeilCoverSimplePoleRegularPart
import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> global meromorphic exponential. Reuse the native logarithmic-model and finite-puncture arguments with proved cover geometry and actual residue values. The global period correction remains open. -/
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

theorem exists_cover_logarithmic_reading (v : Place ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = c) :
    ∃ b : EE, b ∈ v.toValuationSubring ∧
      readDifferential N n radicand A hRadicand hOrders v η =ᶠ[𝓝[≠] (0 : ℂ)] fun z => c * z⁻¹ + chartRead N n radicand A hRadicand hOrders v b z := by
  let b := v.differentialCoeff η - algebraMap ℂ EE c * v.uniformizer⁻¹
  refine ⟨b, cover_simple_pole_regular_part N n radicand v η hη c hc, ?_⟩
  have hs : v.differentialCoeff η = algebraMap ℂ EE c * v.uniformizer⁻¹ + b := by
    dsimp [b]
    ring
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N n radicand A hRadicand hOrders v) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (place_spec N n radicand A hRadicand hOrders v).1)
  filter_upwards [hb, chartRead_add N n radicand A hRadicand hOrders v (algebraMap ℂ EE c * v.uniformizer⁻¹) b,
    chartRead_mul N n radicand A hRadicand hOrders v (algebraMap ℂ EE c) v.uniformizer⁻¹,
    chartRead_inv N n radicand A hRadicand hOrders v v.uniformizer_ne_zero] with z hz ha hm hi
  rw [readDifferential_eq_coefficient N n radicand A hRadicand hOrders v η hz, hs, ha, Pi.add_apply,
    hm, Pi.mul_apply, hi, Pi.inv_apply, chartRead_algebraMap, chartRead_uniformizer N n radicand A hRadicand hOrders v hz]

theorem exists_cover_logarithmic_primitive (v : Place ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = c) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N n radicand A hRadicand hOrders v ∧ ∃ Ψ : ℂ → ℂ,
      AnalyticAt ℂ Ψ 0 ∧ ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
        HasDerivAt Ψ (readDifferential N n radicand A hRadicand hOrders v η z - c * z⁻¹) z := by
  obtain ⟨b, hb, hread⟩ := exists_cover_logarithmic_reading N n radicand A hRadicand hOrders v η hη c hc
  have ha := analyticAt_place_reading N n radicand A hRadicand hOrders v hb
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hread
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (ha.eventually_analyticAt.and hread)
  let r' := min r (placeRadius N n radicand A hRadicand hOrders v) / 2
  have hr' : 0 < r' := half_pos (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1)
  have hsub : ball (0 : ℂ) r' ⊆ ball 0 r :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1))).trans (min_le_left _ _))
  have hd : DifferentiableOn ℂ (chartRead N n radicand A hRadicand hOrders v b) (ball 0 r') :=
    fun z hz => (hball z (hsub hz)).1.differentiableAt.differentiableWithinAt
  obtain ⟨Ψ, hΨ⟩ := hd.isExactOn_ball
  refine ⟨r', hr', (half_lt_self (lt_min hr (place_spec N n radicand A hRadicand hOrders v).1)).trans_le (min_le_right _ _),
    Ψ, ?_, fun z hz hn => ?_⟩
  · exact DifferentiableOn.analyticAt
      (fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt) (ball_mem_nhds 0 hr')
  · have he := (hball z (hsub hz)).2 hn
    rw [he, add_sub_cancel_left]
    exact hΨ z hz


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

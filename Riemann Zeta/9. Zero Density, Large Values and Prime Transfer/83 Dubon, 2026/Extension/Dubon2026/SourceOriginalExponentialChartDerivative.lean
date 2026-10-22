import Dubon2026.SourceOriginalRegularChartReadingAt
import Dubon2026.SourceOriginalExponentialLocalTransport

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic gluing. Exact exponential path transport differentiates to the
original differential reading times the function at every coordinate point
outside the divisor support. Finite-support avoidance and actual local
regularity construct a suitable primitive neighborhood.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem hasDerivAt_original_exponential_chart (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ F → ℂ)
    (htrans : ∀ (P Q : Place ℂ F) (σ : Path P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N η σ))
    (v : Place ℂ F) {z₀ : ℂ} (hz₀ : z₀ ∈ ball 0 (placeRadius N v))
    (hD₀ : D (placeFamily N v z₀) = 0) :
    HasDerivAt (fun z => g (placeFamily N v z))
      (readDifferential N v η z₀ * g (placeFamily N v z₀)) z₀ := by
  letI := place_t2Space N
  have hP : placeFamily N v z₀ ∈ (D.support : Set (Place ℂ F))ᶜ :=
    Finsupp.notMem_support_iff.mpr hD₀
  have hp : ∀ᶠ P in 𝓝 (placeFamily N v z₀), D P = 0 := by
    filter_upwards [D.support.finite_toSet.isClosed.isOpen_compl.mem_nhds hP] with P h
    exact Finsupp.notMem_support_iff.mp h
  have hc : ContinuousAt (placeFamily N v) z₀ :=
    (continuousOn_placeFamily N v).continuousAt (isOpen_ball.mem_nhds hz₀)
  have ha := analyticAt_readDifferential_at_of_coeff_mem N v η hz₀
    (original_coeff_regular_off_divisor N D η hη hres _ hD₀)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((ha.eventually_analyticAt.and (hc.eventually hp)).and (isOpen_ball.mem_nhds hz₀))
  have hd : DifferentiableOn ℂ (readDifferential N v η) (ball z₀ r) :=
    fun z hz => (hball z hz).1.1.differentiableAt.differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := hd.isExactOn_ball
  have hform : (fun z => g (placeFamily N v z)) =ᶠ[𝓝 z₀]
      fun z => g (placeFamily N v z₀) * Complex.exp (Φ z - Φ z₀) := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact original_exponential_local_transport N D η hη hres g htrans v isOpen_ball
      ((convex_ball z₀ r).isPathConnected ⟨z₀, mem_ball_self hr⟩)
      (fun z hz => (hball z hz).2) (fun z hz => (hball z hz).1.2) Φ hΦ (mem_ball_self hr) hz
  have hf : HasDerivAt (fun z => g (placeFamily N v z₀) * Complex.exp (Φ z - Φ z₀))
      (readDifferential N v η z₀ * g (placeFamily N v z₀)) z₀ := by
    convert (((hΦ z₀ (mem_ball_self hr)).sub_const (Φ z₀)).cexp.const_mul
      (g (placeFamily N v z₀))) using 1
    simp only [sub_self, Complex.exp_zero, one_mul, mul_comm]
  exact hf.congr_of_eventuallyEq hform

end
end Dubon2026.SourceFunctionField.OriginalChart

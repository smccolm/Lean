import Dubon2026.SourceOriginalWeilCoverRegularChartReadingAt
import Dubon2026.SourceOriginalWeilCoverExponentialLocalTransport

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period principality. The native exponential argument is applied to the actual cover with constructed residue data, paths and local models. Integral loop periods remain an explicit upstream hypothesis; their correction and the full Abel converse are not asserted here. -/
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


theorem hasDerivAt_cover_exponential_chart (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ EE → ℂ)
    (htrans : ∀ (P Q : Place ℂ EE) (σ : CoverPath P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N n radicand A hRadicand hOrders η σ))
    (v : Place ℂ EE) {z₀ : ℂ} (hz₀ : z₀ ∈ ball 0 (placeRadius N n radicand A hRadicand hOrders v))
    (hD₀ : D (placeFamily N n radicand A hRadicand hOrders v z₀) = 0) :
    HasDerivAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z))
      (readDifferential N n radicand A hRadicand hOrders v η z₀ * g (placeFamily N n radicand A hRadicand hOrders v z₀)) z₀ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  letI := place_t2Space N n radicand A hRadicand hOrders
  have hP : placeFamily N n radicand A hRadicand hOrders v z₀ ∈ (D.support : Set (Place ℂ EE))ᶜ :=
    Finsupp.notMem_support_iff.mpr hD₀
  have hp : ∀ᶠ P in 𝓝 (placeFamily N n radicand A hRadicand hOrders v z₀), D P = 0 := by
    filter_upwards [D.support.finite_toSet.isClosed.isOpen_compl.mem_nhds hP] with P h
    exact Finsupp.notMem_support_iff.mp h
  have hc : ContinuousAt (placeFamily N n radicand A hRadicand hOrders v) z₀ :=
    (continuousOn_placeFamily N n radicand A hRadicand hOrders v).continuousAt (isOpen_ball.mem_nhds hz₀)
  have ha := analyticAt_readDifferential_at_of_coeff_mem N n radicand A hRadicand hOrders v η hz₀
    (cover_coeff_regular_off_divisor N n radicand D η hη hres _ hD₀)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((ha.eventually_analyticAt.and (hc.eventually hp)).and (isOpen_ball.mem_nhds hz₀))
  have hd : DifferentiableOn ℂ (readDifferential N n radicand A hRadicand hOrders v η) (ball z₀ r) :=
    fun z hz => (hball z hz).1.1.differentiableAt.differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := hd.isExactOn_ball
  have hform : (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) =ᶠ[𝓝 z₀]
      fun z => g (placeFamily N n radicand A hRadicand hOrders v z₀) * Complex.exp (Φ z - Φ z₀) := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact cover_exponential_local_transport N n radicand A hRadicand hOrders D η hη hres g htrans v isOpen_ball
      ((convex_ball z₀ r).isPathConnected ⟨z₀, mem_ball_self hr⟩)
      (fun z hz => (hball z hz).2) (fun z hz => (hball z hz).1.2) Φ hΦ (mem_ball_self hr) hz
  have hf : HasDerivAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z₀) * Complex.exp (Φ z - Φ z₀))
      (readDifferential N n radicand A hRadicand hOrders v η z₀ * g (placeFamily N n radicand A hRadicand hOrders v z₀)) z₀ := by
    convert (((hΦ z₀ (mem_ball_self hr)).sub_const (Φ z₀)).cexp.const_mul
      (g (placeFamily N n radicand A hRadicand hOrders v z₀))) using 1
    simp only [sub_self, Complex.exp_zero, one_mul, mul_comm]
  exact hf.congr_of_eventuallyEq hform


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

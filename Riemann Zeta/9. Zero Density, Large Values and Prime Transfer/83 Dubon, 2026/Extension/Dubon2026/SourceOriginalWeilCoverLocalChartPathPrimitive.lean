import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives
import Dubon2026.SourceOriginalWeilCoverChartPathIntegrals

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


theorem isPrimitiveAlong_of_local_chart_primitive (ω : Ω[EE⁄ℂ])
    (v : Place ℂ EE) {W : Set ℂ} (hW : IsOpen W) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N n radicand A hRadicand hOrders v ω z) z)
    {P Q : Place ℂ EE} (γ : CoverPath P Q)
    (hγ : ∀ t, γ t ∈ (placeChart N n radicand A hRadicand hOrders v).source)
    (hγW : ∀ t, placeChart N n radicand A hRadicand hOrders v (γ t) ∈ W)
    (hω : ∀ t, (γ t).differentialCoeff ω ∈ (γ t).toValuationSubring) :
    IsPrimitiveAlong N n radicand A hRadicand hOrders ω γ (fun t => Φ (placeChart N n radicand A hRadicand hOrders v (γ t))) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  intro t₀
  let T := chartRead N n radicand A hRadicand hOrders (γ t₀) v.uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N n radicand A hRadicand hOrders (γ t₀)
    (uniformizer_regular_on_chart N n radicand A hRadicand hOrders v (γ t₀) (hγ t₀))
  have hT0 : T 0 ∈ W := by
    change (placeFamily N n radicand A hRadicand hOrders (γ t₀) 0).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand _) v.uniformizer ∈ _
    rw [(place_spec N n radicand A hRadicand hOrders (γ t₀)).2.1]
    exact hγW t₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ W :=
    hT.continuousAt.eventually (hW.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · rw [placeChart_self]
    filter_upwards [readDifferential_change_of_coeff_mem N n radicand A hRadicand hOrders v (γ t₀) ω (hω t₀) (hγ t₀),
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, γ t ∈ (placeChart N n radicand A hRadicand hOrders (γ t₀)).source :=
      γ.continuous.continuousAt.eventually (placeChart_source_mem_nhds N n radicand A hRadicand hOrders (γ t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N n radicand A hRadicand hOrders v (γ t)) =
      Φ (placeChart N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders (γ t₀) (placeChart N n radicand A hRadicand hOrders (γ t₀) (γ t))))
    rw [show placeFamily N n radicand A hRadicand hOrders (γ t₀) (placeChart N n radicand A hRadicand hOrders (γ t₀) (γ t)) = γ t from
      (placeChart N n radicand A hRadicand hOrders (γ t₀)).left_inv ht]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

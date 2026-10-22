import Dubon2026.SourceOriginalLocalRegularPrimitives
import Dubon2026.SourceOriginalChartPathIntegrals

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential -> local transport. A primitive on an open
part of an original chart represents the actual integral along paths there.
Only regularity on the path is required. Existing exact local differential
transitions supply the primitive in each path-centered chart.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem isPrimitiveAlong_of_local_chart_primitive (ω : Ω[F⁄ℂ])
    (v : Place ℂ F) {W : Set ℂ} (hW : IsOpen W) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N v ω z) z)
    {P Q : Place ℂ F} (γ : Path P Q)
    (hγ : ∀ t, γ t ∈ (placeChart N v).source)
    (hγW : ∀ t, placeChart N v (γ t) ∈ W)
    (hω : ∀ t, (γ t).differentialCoeff ω ∈ (γ t).toValuationSubring) :
    IsPrimitiveAlong N ω γ (fun t => Φ (placeChart N v (γ t))) := by
  intro t₀
  let T := chartRead N (γ t₀) v.uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N (γ t₀)
    (uniformizer_regular_on_chart N v (γ t₀) (hγ t₀))
  have hT0 : T 0 ∈ W := by
    change originalPlaceEval N ℂ (placeFamily N (γ t₀) 0) v.uniformizer ∈ _
    rw [(place_spec N (γ t₀)).2.1]
    exact hγW t₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ W :=
    hT.continuousAt.eventually (hW.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · rw [placeChart_self]
    filter_upwards [readDifferential_change_of_coeff_mem N v (γ t₀) ω (hω t₀) (hγ t₀),
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, γ t ∈ (placeChart N (γ t₀)).source :=
      γ.continuous.continuousAt.eventually (placeChart_source_mem_nhds N (γ t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N v (γ t)) =
      Φ (placeChart N v (placeFamily N (γ t₀) (placeChart N (γ t₀) (γ t))))
    rw [show placeFamily N (γ t₀) (placeChart N (γ t₀) (γ t)) = γ t from
      (placeChart N (γ t₀)).left_inv ht]

end
end Dubon2026.SourceFunctionField.OriginalChart

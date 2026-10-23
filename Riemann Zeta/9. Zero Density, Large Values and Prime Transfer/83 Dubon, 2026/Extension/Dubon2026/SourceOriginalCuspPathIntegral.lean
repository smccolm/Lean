import Dubon2026.SourceOriginalCuspChartPrimitives
import Dubon2026.SourceOriginalPathIntegral

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual period
identification. A path in the upper half-plane maps continuously to the
original curve. The normalized Eichler primitive is a primitive along
that actual path in the existing original-chart sense, so its endpoint
difference equals the actual original differential path integral.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem original_cusp_primitive_isPrimitiveAlong
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {τ₀ τ₁ : ℍ} (γ : Path τ₀ τ₁) :
    IsPrimitiveAlong N ω.val (γ.map (originalAnalyticPlace_continuous N))
      (fun t => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω) (γ t)) := by
  intro s
  let τ := γ s
  let G := sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω)
  obtain ⟨Φ, hΦ⟩ := exists_readDifferential_primitive_on_chart N
    (originalAnalyticPlace N τ) ω.val ω.property
  have hΦ₀ : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasDerivAt Φ (readDifferential N (originalAnalyticPlace N τ) ω.val z) z := by
    filter_upwards [ball_mem_nhds 0 (place_spec N (originalAnalyticPlace N τ)).1] with z hz
    exact hΦ z hz
  refine ⟨fun z => Φ z + (G τ - Φ 0), ?_, ?_⟩
  · change ∀ᶠ z in 𝓝 (placeChart N (originalAnalyticPlace N τ) (originalAnalyticPlace N τ)), _
    rw [placeChart_self]
    exact hΦ₀.mono fun z hz => hz.add_const _
  · have hc : ContinuousAt (fun t : unitInterval => (γ t : ℂ)) s :=
      UpperHalfPlane.continuous_coe.continuousAt.comp γ.continuous.continuousAt
    have he := hc.eventually (original_chart_primitive_cusp_comparison N τ ω Φ hΦ₀)
    filter_upwards [he] with t ht
    change G (γ t) = Φ (placeChart N (originalAnalyticPlace N τ)
      (originalAnalyticPlace N (γ t))) + (G τ - Φ 0)
    change Φ (placeChart N (originalAnalyticPlace N τ)
      (originalAnalyticPlace N (ofComplex (γ t)))) - Φ 0 = G (ofComplex (γ t)) - G τ at ht
    rw [ofComplex_apply] at ht
    linear_combination -ht

theorem original_pathIntegral_eq_cusp_primitive
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {τ₀ τ₁ : ℍ} (γ : Path τ₀ τ₁) :
    pathIntegral N ω.val (γ.map (originalAnalyticPlace_continuous N)) =
      sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω) τ₁ -
        sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω) τ₀ := by
  rw [pathIntegral_eq_of_isPrimitiveAlong N (original_cusp_primitive_isPrimitiveAlong N ω γ),
    γ.target, γ.source]

end
end Dubon2026.SourceFunctionField.OriginalChart

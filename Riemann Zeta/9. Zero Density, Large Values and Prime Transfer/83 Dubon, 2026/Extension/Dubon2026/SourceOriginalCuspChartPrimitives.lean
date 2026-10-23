import Dubon2026.SourceOriginalRegularDifferentialPullback
import Dubon2026.SourceWeightTwoAnalyticPrimitive

/-! DUB-17/18 -> original Picard-period Hecke comparison -> equality of
actual path periods. Every original chart primitive pulls back to the
already constructed normalized Eichler primitive, up to its uniquely
determined additive constant. The differential identity is proved in the
preceding module; local primitive uniqueness is reused unchanged.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem original_chart_primitive_cusp_comparison (τ : ℍ)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (Φ : ℂ → ℂ)
    (hΦ : ∀ᶠ u in 𝓝 (0 : ℂ),
      HasDerivAt Φ (readDifferential N (originalAnalyticPlace N τ) ω.val u) u) :
    ∀ᶠ z : ℂ in 𝓝 (τ : ℂ),
      Φ (analyticChartCoordinate N τ z) - Φ 0 =
        sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω) (ofComplex z) -
          sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N ω) τ := by
  let f := originalRegularCuspEquiv N ω
  let t := analyticChartCoordinate N τ
  have ht : Tendsto t (𝓝 (τ : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [analyticChartCoordinate_self] using
      (analyticChartCoordinate_analyticAt N τ).continuousAt.tendsto
  have h₁ : ∀ᶠ z in 𝓝 (τ : ℂ), HasDerivAt (Φ ∘ t) (f (ofComplex z)) z := by
    filter_upwards [ht.eventually hΦ,
      (analyticChartCoordinate_analyticAt N τ).eventually_analyticAt,
      readDifferential_analyticChartCoordinate N τ ω] with z hz htz he
    exact ((hz.comp z htz.differentiableAt.hasDerivAt).congr_deriv he)
  have h₂ : ∀ᶠ z : ℂ in 𝓝 (τ : ℂ),
      HasDerivAt (sourceWeightTwoPrimitive 1 f ∘ ofComplex) (f (ofComplex z)) z := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hd := sourceWeightTwoPrimitive_hasDerivAt f (by norm_num)
      (ModularRatios.one_mem_strictPeriods N) (⟨z, hz⟩ : ℍ)
    simpa only [ofComplex_apply_of_im_pos hz] using hd
  filter_upwards [eventually_sub_eq_of_hasDerivAt h₁ h₂] with z hz
  dsimp only [Function.comp_apply] at hz
  rw [show t τ = 0 from analyticChartCoordinate_self N τ, ofComplex_apply] at hz
  linear_combination hz

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalDifferentialRegularNeighborhood
import Dubon2026.SourceMeromorphicRemovableCharts

/-! DUB-17/18 -> raw reciprocity -> local cell coefficient calculus.
The existing Kaehler germ identity and actual uniformizer charts give the
one-form transformation law near every regular original place. Native analytic
chart transitions and the literal coordinate derivative replace the general
external curve-coordinate algebra in the source coeffIn calculation.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology Manifold ContDiff
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology placeChartedSpace
local notation "F" => modularFunctionFieldOver N ℂ

theorem one_form_law_at (Q : Place ℂ F) (θ : Ω[F⁄ℂ])
    {y : ℂ} (hy : y ∈ ball 0 (placeRadius N Q))
    (hyr : (placeFamily N Q y).differentialCoeff θ ∈ (placeFamily N Q y).toValuationSubring) :
    readDifferential N Q θ y =
      readDifferential N (placeFamily N Q y) θ 0 *
        deriv (extChartAt 𝓘(ℂ, ℂ) (placeFamily N Q y) ∘
          (extChartAt 𝓘(ℂ, ℂ) Q).symm) y := by
  letI := place_isManifold N
  haveI := original_place_dCoordGenerates N ℂ Q
  let Q' := placeFamily N Q y
  have hyh := chart_differentialCoeff_regular_at N Q Q' θ hyr ⟨y, hy, rfl⟩
  let T : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q' ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm
  have hyt : y ∈ (extChartAt 𝓘(ℂ, ℂ) Q).target := by
    simpa using (show y ∈ (chartAt ℂ Q).target from hy)
  have hQt : (extChartAt 𝓘(ℂ, ℂ) Q).symm y ∈ (extChartAt 𝓘(ℂ, ℂ) Q').source := by
    rw [extPlaceChart_symm_apply]
    exact mem_extChartAt_source Q'
  have hTa : AnalyticAt ℂ T y := MeromorphicCompact.analyticAt_transition Q' Q hyt hQt
  have hTy : T y = 0 := by
    dsimp only [T, Function.comp_apply]
    rw [extPlaceChart_symm_apply]
    exact extPlaceChart_self N Q'
  have hπ : Q.uniformizer ∈ Q'.toValuationSubring :=
    uniformizer_regular_on_chart N Q Q' ⟨y, hy, rfl⟩
  have h2 := (readDifferential_eq_expression_of_coeff_mem N Q' θ hyr
    (Q.differentialCoeff θ) Q.uniformizer hyh hπ
      (Q.differentialCoeff_smul_dCoord θ).symm).self_of_nhds
  have hcomp : chartRead N Q Q.uniformizer =ᶠ[𝓝 y] chartRead N Q' Q.uniformizer ∘ T := by
    filter_upwards [MeromorphicCompact.eventually_symm_mem_source hyt hQt] with z hz
    rw [← chartRead_eq_extChartAt, Function.comp_apply, ← chartRead_eq_extChartAt]
    change originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) Q).symm z) Q.uniformizer =
      originalPlaceEval N ℂ ((extChartAt 𝓘(ℂ, ℂ) Q').symm
        (extChartAt 𝓘(ℂ, ℂ) Q' ((extChartAt 𝓘(ℂ, ℂ) Q).symm z))) Q.uniformizer
    rw [(extChartAt 𝓘(ℂ, ℂ) Q').left_inv hz]
  have hπa := analyticAt_place_reading N Q' hπ
  have hπd : HasDerivAt (chartRead N Q' Q.uniformizer)
      (deriv (chartRead N Q' Q.uniformizer) 0) (T y) := by
    rw [hTy]
    exact hπa.differentiableAt.hasDerivAt
  have hd : deriv (chartRead N Q' Q.uniformizer) 0 * deriv T y = 1 := by
    rw [← (hπd.comp y hTa.differentiableAt.hasDerivAt).deriv, ← hcomp.deriv_eq]
    exact deriv_chartRead_uniformizer N Q hy
  have hval : chartRead N Q' (Q.differentialCoeff θ) 0 =
      chartRead N Q (Q.differentialCoeff θ) y := by
    change originalPlaceEval N ℂ (placeFamily N Q' 0) _ = originalPlaceEval N ℂ Q' _
    rw [(place_spec N Q').2.1]
  rw [readDifferential_eq_coefficient N Q θ hy, h2]
  change _ = (chartRead N Q' (Q.differentialCoeff θ) 0 *
    deriv (chartRead N Q' Q.uniformizer) 0) * deriv T y
  rw [mul_assoc, hd, mul_one, hval]


theorem one_form_law (Q : Place ℂ F) (θ : Ω[F⁄ℂ])
    (hθ : Q.differentialCoeff θ ∈ Q.toValuationSubring) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      AnalyticAt ℂ (readDifferential N Q θ) y ∧
      readDifferential N Q θ y =
        readDifferential N ((extChartAt 𝓘(ℂ, ℂ) Q).symm y) θ
          (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)
            ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)) *
          deriv (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y) ∘
            (extChartAt 𝓘(ℂ, ℂ) Q).symm) y := by
  rw [extPlaceChart_self]
  have hr : ∀ᶠ y in 𝓝 (0 : ℂ),
      (placeFamily N Q y).differentialCoeff θ ∈ (placeFamily N Q y).toValuationSubring := by
    have hc := placeFamily_continuousAt_zero N Q
    rw [ContinuousAt, (place_spec N Q).2.1] at hc
    exact hc.eventually (eventually_differentialCoeff_mem N Q θ hθ)
  filter_upwards [hr, (analyticAt_readDifferential_of_coeff_mem N Q θ hθ).eventually_analyticAt,
    ball_mem_nhds (0 : ℂ) (place_spec N Q).1] with y hyr hya hy
  refine ⟨hya, ?_⟩
  rw [extPlaceChart_symm_apply, extPlaceChart_self]
  exact one_form_law_at N Q θ hy hyr

end
end Dubon2026.SourceFunctionField.OriginalChart

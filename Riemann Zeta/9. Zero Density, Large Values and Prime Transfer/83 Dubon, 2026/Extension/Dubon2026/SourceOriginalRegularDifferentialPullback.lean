import Dubon2026.SourceOriginalAnalyticChartCoordinate
import Dubon2026.SourceOriginalEvaluationRealizationGerms
import Dubon2026.SourceOriginalRegularCuspGlobalGerms

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual regular
differential/cusp period comparison. The chart pullback equals the native
cusp form selected by the proved germ equivalence. The Kaehler expression
in the original j-coordinate and the ordinary chain rule supply the
identity, with no unramified-point restriction.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem chartRead_analyticChartCoordinate_eventuallyEq_realize (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ) :
    (fun z => chartRead N (originalAnalyticPlace N τ) f (analyticChartCoordinate N τ z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize N (f : LaurentSeries ℂ) (ofComplex z) := by
  filter_upwards [(chartRead_analyticChartCoordinate N τ).filter_mono nhdsWithin_le_nhds,
    originalPlaceEval_eventuallyEq_realize N f τ] with z hz hr
  exact (hz f).trans hr

theorem readDifferential_analyticChartCoordinate_germ (τ : ℍ)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    (fun z => readDifferential N (originalAnalyticPlace N τ) ω.val
      (analyticChartCoordinate N τ z) * deriv (analyticChartCoordinate N τ) z) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => originalRegularCuspEquiv N ω (ofComplex z) := by
  let v := originalAnalyticPlace N τ
  let t := analyticChartCoordinate N τ
  let x := (originalDifferentialCoordinateEquiv N).symm ω.val
  have he : ω.val = x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) :=
    ((originalDifferentialCoordinateEquiv N).apply_symm_apply ω.val).symm
  have ht := analyticChartCoordinate_tendsto_nhdsNE N τ
  have hj : (fun z => chartRead N v (jOver N ℂ) (t z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      JMultiplicity.jf ∘ ofComplex := by
    simpa only [realize_jOver] using
      chartRead_analyticChartCoordinate_eventuallyEq_realize N τ (jOver N ℂ)
  filter_upwards [ht.eventually (readDifferential_eq_expression_germ N v ω.val x (jOver N ℂ) he),
    ht.eventually (eventually_differentiableAt_chartRead N v (jOver N ℂ)),
    (analyticChartCoordinate_analyticAt N τ).eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hj.nhdsNE_deriv, chartRead_analyticChartCoordinate_eventuallyEq_realize N τ x,
    originalRegularCuspEquiv_eventuallyEq N τ ω] with z hex hjd htd hder hx hf
  change readDifferential N v ω.val (t z) * deriv t z = _
  rw [hex]
  rw [hf, ← hx]
  have hchain : deriv (fun u => chartRead N v (jOver N ℂ) (t u)) z =
      deriv (chartRead N v (jOver N ℂ)) (t z) * deriv t z :=
    (hjd.hasDerivAt.comp z htd.differentiableAt.hasDerivAt).deriv
  rw [← hder, hchain]
  exact mul_assoc _ _ _

theorem readDifferential_analyticChartCoordinate (τ : ℍ)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    (fun z => readDifferential N (originalAnalyticPlace N τ) ω.val
      (analyticChartCoordinate N τ z) * deriv (analyticChartCoordinate N τ) z) =ᶠ[𝓝 (τ : ℂ)]
      fun z => originalRegularCuspEquiv N ω (ofComplex z) := by
  have ht := analyticChartCoordinate_analyticAt N τ
  have hr : AnalyticAt ℂ (readDifferential N (originalAnalyticPlace N τ) ω.val)
      (analyticChartCoordinate N τ τ) := by
    rw [analyticChartCoordinate_self]
    exact analyticAt_readDifferential N _ ω.val ω.property
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hr.comp ht).mul ht.deriv).continuousAt
    (JMultiplicity.analyticAt_comp (originalRegularCuspEquiv N ω).holo' τ).continuousAt).mp
      (readDifferential_analyticChartCoordinate_germ N τ ω)

end
end Dubon2026.SourceFunctionField.OriginalChart

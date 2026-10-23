import Dubon2026.SourceOriginalAnalyticPlaceContinuity
import Dubon2026.SourceOriginalChartDifferentials
import Dubon2026.SourceOriginalPathLocalPrimitives

/-! DUB-17/18 -> original Picard-period Hecke comparison -> pullback of
regular differentials. The actual uniformizer coordinate of the analytic
place map is analytic, tends to zero through nonzero values on punctured
neighborhoods, and recovers every original field evaluation through the
existing chart. Its exact order is the already proved ramification index.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

/-- The original place chart pulled back along the actual analytic place map. -/
def analyticChartCoordinate (τ : ℍ) (z : ℂ) : ℂ :=
  placeChart N (originalAnalyticPlace N τ) (originalAnalyticPlace N (ofComplex z))

theorem analyticChartCoordinate_analyticAt (τ : ℍ) :
    AnalyticAt ℂ (analyticChartCoordinate N τ) (τ : ℂ) := by
  apply (originalPlaceEval_analyticAt_iff N _ τ).mpr
  exact (originalAnalyticPlace N τ).uniformizerSubring.property

theorem analyticChartCoordinate_self (τ : ℍ) : analyticChartCoordinate N τ τ = 0 := by
  change placeChart N (originalAnalyticPlace N τ) (originalAnalyticPlace N (ofComplex τ)) = 0
  rw [ofComplex_apply, placeChart_self]

theorem analyticChartCoordinate_tendsto_nhdsNE (τ : ℍ) :
    Tendsto (analyticChartCoordinate N τ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  have ha := analyticChartCoordinate_analyticAt N τ
  have ho : meromorphicOrderAt (analyticChartCoordinate N τ) (τ : ℂ) ≠ ⊤ := by
    rw [show meromorphicOrderAt (analyticChartCoordinate N τ) (τ : ℂ) =
        (((originalAnalyticRamification N τ : ℤ) *
          (originalAnalyticPlace N τ).ord (originalAnalyticPlace N τ).uniformizer : ℤ) :
            WithTop ℤ) from originalPlaceEval_meromorphicOrderAt N _
              (originalAnalyticPlace N τ).uniformizer_ne_zero τ]
    exact WithTop.coe_ne_top
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ha.meromorphicAt).mp ho
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, hn⟩
  simpa only [analyticChartCoordinate_self] using
    ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem chartRead_analyticChartCoordinate (τ : ℍ) :
    ∀ᶠ z : ℂ in 𝓝 (τ : ℂ), ∀ f : modularFunctionFieldOver N ℂ,
      chartRead N (originalAnalyticPlace N τ) f (analyticChartCoordinate N τ z) =
        originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f := by
  have hm := (originalAnalyticPlace_ofComplex_continuousAt N τ).eventually
    (by simpa only [ofComplex_apply] using
      placeChart_source_mem_nhds N (originalAnalyticPlace N τ))
  filter_upwards [hm] with z hz f
  change originalPlaceEval N ℂ
    ((placeChart N (originalAnalyticPlace N τ)).symm
      (placeChart N (originalAnalyticPlace N τ) (originalAnalyticPlace N (ofComplex z)))) f = _
  rw [(placeChart N (originalAnalyticPlace N τ)).left_inv hz]

end
end Dubon2026.SourceFunctionField.OriginalChart

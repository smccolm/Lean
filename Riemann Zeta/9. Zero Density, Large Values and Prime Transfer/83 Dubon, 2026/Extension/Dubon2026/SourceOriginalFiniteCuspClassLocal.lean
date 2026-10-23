import Dubon2026.SourceOriginalFiniteCuspClass
import Dubon2026.SourceOriginalRamifiedChartLift

/-! DUB-17/18 -> original Picard-period Hecke comparison -> reverse
period-lattice inclusion. Near every finite original place, the actual
modular primitive class varies by the vector of the original chart
primitives. Convergent ramified lifts and the already proved pullback
comparison supply this identity also at elliptic points. This is the
local input for comparing genuine loop periods with modular periods.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem originalFiniteCuspClass_chart_primitive {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (τ : ℍ) (Φ : Fin n → ℂ → ℂ)
    (hΦ : ∀ i, ∀ᶠ u in 𝓝 (0 : ℂ),
      HasDerivAt (Φ i) (readDifferential N (originalAnalyticPlace N τ) (b i).val u) u) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      ∀ hz : jOver N ℂ ∈ (placeFamily N (originalAnalyticPlace N τ) z).toValuationSubring,
        originalFiniteCuspClass N b ⟨placeFamily N (originalAnalyticPlace N τ) z, hz⟩ -
          originalAnalyticCuspClass N b τ =
            (originalCuspPeriodLattice N b).mkQ (fun i => Φ i z - Φ i 0) := by
  obtain ⟨r, hr, hp⟩ := exists_original_chart_analytic_lift N τ
  have hcomp : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ∀ i,
      Φ i (analyticChartCoordinate N τ (r z)) - Φ i 0 =
        sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) (ofComplex (r z)) -
          sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ :=
    Filter.eventually_all.mpr fun i => hr.eventually
      (original_chart_primitive_cusp_comparison N τ (b i) (Φ i) (hΦ i))
  filter_upwards [hp, hcomp,
    ball_mem_nhds (0 : ℂ) (place_spec N (originalAnalyticPlace N τ)).1] with z hpz hcz hball hz
  have ht : analyticChartCoordinate N τ (r z) = z := by
    change originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex (r z)))
      (originalAnalyticPlace N τ).uniformizer = z
    rw [hpz]
    exact place_eval_uniformizer N _ hball
  rw [originalFiniteCuspClass_apply N b _ (ofComplex (r z)) hpz,
    originalAnalyticCuspClass, originalAnalyticCuspClass, ← map_sub]
  congr 1
  funext i
  have hi := hcz i
  rw [ht] at hi
  simp only [Pi.sub_apply]
  linear_combination -hi

end
end Dubon2026.SourceFunctionField.OriginalChart

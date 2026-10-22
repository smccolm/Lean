import Dubon2026.SourceOriginalAnalyticEvaluation
import Dubon2026.SourceOriginalEllipticFibers
import Dubon2026.SourcePowerFiberAnalyticDescent

/-! DUB-17/18 -> original torsion cardinality -> complex place charts.
The actual modular stabilizer discharges local power-fiber invariance.
Choosing roots of the ramified coordinate therefore gives a family of
literal original places through the prescribed place. Every original
regular function has analytic residue values on this family, and the
power pullback is its previously proved analytic realization. This
includes elliptic ramification; no invariance or analytic model is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter EllipticCoordinate
open scoped Topology

/-- Actual original places parameterized through the ramification power coordinate. -/
def originalRamifiedPlace (N : ℕ) [NeZero N] (τ : ℍ) (z : ℂ) :
    SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) :=
  originalAnalyticPlace N (ofComplex (param τ (PowerDescent.root
    (originalAnalyticRamification N τ) (originalAnalyticRamification_pos N τ).ne' z)))

theorem originalRamifiedPlace_zero (N : ℕ) [NeZero N] (τ : ℍ) :
    originalRamifiedPlace N τ 0 = originalAnalyticPlace N τ := by
  rw [originalRamifiedPlace, PowerDescent.root_zero, param_zero, ofComplex_apply]

theorem originalRamifiedPlace_regular_analytic (N : ℕ) [NeZero N] (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ)
    (hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring) :
    AnalyticAt ℂ (fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),
        originalPlaceEval N ℂ (originalRamifiedPlace N τ (z ^ originalAnalyticRamification N τ)) f =
          originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex (param τ z))) f := by
  let F : ℂ → ℂ := fun z => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex (param τ z))) f
  have ha : AnalyticAt ℂ F 0 := by
    have ha' : AnalyticAt ℂ
        (fun z : ℂ => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex z)) f) (param τ 0) := by
      rw [param_zero]
      exact (originalPlaceEval_analyticAt_iff N f τ).mpr hf
    exact ha'.comp (analyticAt_param τ)
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨R, hR, hbound⟩ := Metric.eventually_nhds_iff_ball.mp ((param_im_pos_eventually τ).and hne)
  have hInv : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R →
      u ^ originalAnalyticRamification N τ = v ^ originalAnalyticRamification N τ → F u = F v := by
    intro u v hu hv hpow
    have hpu := hbound u (by simpa only [Metric.mem_ball, dist_zero_right] using hu)
    have hpv := hbound v (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
    have hplace := place_eq_of_coord_power_eq N τ (ofComplex (param τ u)) (ofComplex (param τ v))
      (by simpa only [ofComplex_apply_of_im_pos hpu.1, ofComplex_apply_of_im_pos hpv.1,
        coord_param τ hpu.2, coord_param τ hpv.2] using hpow)
    exact congrArg (fun P => originalPlaceEval N ℂ P f) hplace
  exact PowerDescent.analyticAt_root_composite (originalAnalyticRamification N τ)
    (originalAnalyticRamification_pos N τ).ne' F ha R hR hInv

end
end Dubon2026.SourceFunctionField

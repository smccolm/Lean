import Dubon2026.SourceGammaOneAnalyticEvaluation
import Dubon2026.SourceGammaOneEllipticFibers
import Dubon2026.SourcePowerFiberAnalyticDescent

/-! DUB-17/18 -> actual Gamma1 period comparison -> complex place charts.
The actual modular stabilizer discharges local power-fiber invariance.
Choosing roots of the ramified coordinate therefore gives a family of
literal original places through the prescribed place. Every original
regular function has analytic residue values on this family, and the
power pullback is its previously proved analytic realization. This
includes elliptic ramification; no invariance or analytic model is assumed.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter EllipticCoordinate CongruenceSubgroup
open scoped Topology

/-- Actual Gamma1 places parameterized through the ramification power coordinate. -/
def ramifiedPlace (N : ℕ) (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ) (z : ℂ) :
    SourceCurve.Place ℂ (functionFieldOver (Gamma1 N) ℂ) :=
  analyticPlace hT (ofComplex (param τ (PowerDescent.root
    (analyticRamification hT τ) (analyticRamification_pos hT τ).ne' z)))

theorem ramifiedPlace_zero (N : ℕ) (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ) :
    ramifiedPlace N hT τ 0 = analyticPlace hT τ := by
  rw [ramifiedPlace, PowerDescent.root_zero, param_zero, ofComplex_apply]

theorem ramifiedPlace_regular_analytic (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ)
    (f : functionFieldOver (Gamma1 N) ℂ)
    (hf : f ∈ (analyticPlace hT τ).toValuationSubring) :
    AnalyticAt ℂ (fun z => placeEval hT (ramifiedPlace N hT τ z) f) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),
        placeEval hT (ramifiedPlace N hT τ (z ^ analyticRamification hT τ)) f =
          placeEval hT (analyticPlace hT (ofComplex (param τ z))) f := by
  let F : ℂ → ℂ := fun z => placeEval hT (analyticPlace hT (ofComplex (param τ z))) f
  have ha : AnalyticAt ℂ F 0 := by
    have ha' : AnalyticAt ℂ
        (fun z : ℂ => placeEval hT (analyticPlace hT (ofComplex z)) f) (param τ 0) := by
      rw [param_zero]
      exact (placeEval_analyticAt_iff hT f τ).mpr hf
    exact ha'.comp (analyticAt_param τ)
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨R, hR, hbound⟩ := Metric.eventually_nhds_iff_ball.mp ((param_im_pos_eventually τ).and hne)
  have hInv : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R →
      u ^ analyticRamification hT τ = v ^ analyticRamification hT τ → F u = F v := by
    intro u v hu hv hpow
    have hpu := hbound u (by simpa only [Metric.mem_ball, dist_zero_right] using hu)
    have hpv := hbound v (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
    have hplace := place_eq_of_coord_power_eq N hT τ (ofComplex (param τ u)) (ofComplex (param τ v))
      (by simpa only [ofComplex_apply_of_im_pos hpu.1, ofComplex_apply_of_im_pos hpv.1,
        coord_param τ hpu.2, coord_param τ hpv.2] using hpow)
    exact congrArg (fun P => placeEval hT P f) hplace
  exact PowerDescent.analyticAt_root_composite (analyticRamification hT τ)
    (analyticRamification_pos hT τ).ne' F ha R hR hInv

end
end Dubon2026.SourceFunctionField.GammaOne

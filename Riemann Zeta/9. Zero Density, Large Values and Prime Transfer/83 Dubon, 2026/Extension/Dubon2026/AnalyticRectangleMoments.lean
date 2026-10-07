import Dubon2026.AnalyticCompactIntegral
import Dubon2026.TwistContourContinuity

/-! # Analytic dependence of the actual rectangle zero-power integrals on complex phases -/

namespace Dubon2026

open Complex Set MeasureTheory
open scoped Topology

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

theorem analyticAt_complexPhase_path_logDeriv (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℂ) (γ ω : ℝ → ℂ) (hγ : Continuous γ) (hω : Continuous ω)
    {b t : ℝ} (hbt : b ≤ t)
    (hn : ∀ v ∈ Icc b t, complexPhaseFamily a N (x, γ v) ≠ 0) :
    AnalyticAt ℂ (fun y => ∫ v in b..t,
      ω v * logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) (γ v)) x := by
  letI : IsFiniteMeasure (volume : Measure (Icc b t)) := ⟨by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let Γ : C(Icc b t, ℂ) := ⟨fun v => γ v, hγ.comp continuous_subtype_val⟩
  let Ω : C(Icc b t, ℂ) := ⟨fun v => ω v, hω.comp continuous_subtype_val⟩
  have hh := analyticAt_integral_compactPhase_logDeriv a N Γ Ω volume x
    (fun v => hn v v.property)
  have he : (fun y => ∫ v : Icc b t, Ω v *
      logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) (Γ v)) =
      (fun y => ∫ v in b..t, ω v *
        logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) (γ v)) := by
    funext y
    dsimp only [Γ, Ω, ContinuousMap.coe_mk]
    rw [integral_subtype measurableSet_Icc (fun v : ℝ => ω v *
      logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) (γ v)),
      integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hbt]
  rwa [he] at hh

theorem analyticAt_complexPhase_rectangle_power_logDeriv (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℂ) {s t : ℂ} (hre : s.re ≤ t.re) (him : s.im ≤ t.im)
    (hn : ∀ w ∈ RectangleBorder s t, complexPhaseFamily a N (x, w) ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun y => RectangleIntegral'
      (fun w => w ^ k * logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) w) s t) x := by
  have h₁ := analyticAt_complexPhase_path_logDeriv a N x
    (fun v : ℝ => (v : ℂ) + s.im * I) (fun v : ℝ => ((v : ℂ) + s.im * I) ^ k)
    (by fun_prop) (by fun_prop) hre
    (fun v hv => hn _ (mapsTo_rectangleBorder_left_im s t (by simpa [uIcc_of_le hre] using hv)))
  have h₂ := analyticAt_complexPhase_path_logDeriv a N x
    (fun v : ℝ => (v : ℂ) + t.im * I) (fun v : ℝ => ((v : ℂ) + t.im * I) ^ k)
    (by fun_prop) (by fun_prop) hre
    (fun v hv => hn _ (mapsTo_rectangleBorder_right_im s t (by simpa [uIcc_of_le hre] using hv)))
  have h₃ := analyticAt_complexPhase_path_logDeriv a N x
    (fun v : ℝ => (t.re : ℂ) + v * I) (fun v : ℝ => ((t.re : ℂ) + v * I) ^ k)
    (by fun_prop) (by fun_prop) him
    (fun v hv => hn _ (mapsTo_rectangleBorder_right_re s t (by simpa [uIcc_of_le him] using hv)))
  have h₄ := analyticAt_complexPhase_path_logDeriv a N x
    (fun v : ℝ => (s.re : ℂ) + v * I) (fun v : ℝ => ((s.re : ℂ) + v * I) ^ k)
    (by fun_prop) (by fun_prop) him
    (fun v hv => hn _ (mapsTo_rectangleBorder_left_re s t (by simpa [uIcc_of_le him] using hv)))
  exact (analyticAt_const (v := (1 / (2 * Real.pi * I) : ℂ))).smul (((h₁.sub h₂).add
    ((analyticAt_const (v := I)).smul h₃)).sub ((analyticAt_const (v := I)).smul h₄))

end

end Dubon2026

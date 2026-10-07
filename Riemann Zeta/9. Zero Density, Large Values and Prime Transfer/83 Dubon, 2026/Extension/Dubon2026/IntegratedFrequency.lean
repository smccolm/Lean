import Dubon2026.RankinGammaPhase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # A real primitive of an actual phase frequency and the exact complex phase -/

namespace Dubon2026

open Complex MeasureTheory

noncomputable section

/-- The genuine integral primitive of a real frequency, based at zero. -/
def integratedFrequency (ν : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, ν u

/-- A continuous actual frequency is the derivative of its integral primitive. -/
theorem hasDerivAt_integratedFrequency {ν : ℝ → ℝ} (hν : Continuous ν) (t : ℝ) :
    HasDerivAt (integratedFrequency ν) (ν t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (hν.intervalIntegrable _ _)
    hν.aestronglyMeasurable.stronglyMeasurableAtFilter hν.continuousAt

/-- The integrated phase has the exact C1 regularity needed by the nonstationary-phase theorem. -/
theorem contDiff_integratedFrequency {ν : ℝ → ℝ} (hν : Continuous ν) :
    ContDiff ℝ 1 (integratedFrequency ν) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_integratedFrequency hν t).differentiableAt, ?_⟩
  have he : deriv (integratedFrequency ν) = ν := funext fun t =>
    (hasDerivAt_integratedFrequency hν t).deriv
  rwa [he]

/-- The actual complex phase is recovered from its differential equation by a proved integrating factor. -/
theorem phase_eq_initial_mul_exp_integratedFrequency {ν : ℝ → ℝ} {z : ℝ → ℂ}
    (hν : Continuous ν)
    (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t) (t : ℝ) :
    z t = z 0 * Complex.exp (I * (integratedFrequency ν t : ℂ)) := by
  let H : ℝ → ℂ := fun u => z u * Complex.exp (-I * (integratedFrequency ν u : ℂ))
  have hd (u : ℝ) : HasDerivAt H 0 u := by
    have ha := (((hasDerivAt_integratedFrequency hν u).ofReal_comp).const_mul (-I)).cexp
    convert (hz u).mul ha using 1
    ring
  have hc : H t = z 0 := by
    have hh := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simpa [H, integratedFrequency] using hh
  calc
    z t = H t * Complex.exp (I * (integratedFrequency ν t : ℂ)) := by
      dsimp [H]
      rw [mul_assoc, ← Complex.exp_add]
      simp
    _ = _ := by rw [hc]

/-- The phase differential equation preserves the actual initial modulus. -/
theorem norm_phase_eq_initial {ν : ℝ → ℝ} {z : ℝ → ℂ} (hν : Continuous ν)
    (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t) (t : ℝ) :
    ‖z t‖ = ‖z 0‖ := by
  rw [phase_eq_initial_mul_exp_integratedFrequency hν hz t, norm_mul, Complex.norm_exp]
  simp

/-- The actual two-Gamma Rankin frequency is continuous on the entire real height line. -/
theorem continuous_rankinGammaFrequency {k : ℤ} (hk : 0 < k) :
    Continuous (rankinGammaFrequency k) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_rankinGammaFrequency hk t).continuousAt

/-- The genuine reflected Gamma quotient equals its initial phase times the actual integrated frequency. -/
theorem rankinGammaPhase_eq_exp_integratedFrequency {k : ℤ} (hk : 0 < k) (t : ℝ) :
    rankinGammaPhase k t = rankinGammaPhase k 0 *
      Complex.exp (I * (integratedFrequency (rankinGammaFrequency k) t : ℂ)) :=
  phase_eq_initial_mul_exp_integratedFrequency (continuous_rankinGammaFrequency hk)
    (hasDerivAt_rankinGammaPhase hk) t

end
end Dubon2026

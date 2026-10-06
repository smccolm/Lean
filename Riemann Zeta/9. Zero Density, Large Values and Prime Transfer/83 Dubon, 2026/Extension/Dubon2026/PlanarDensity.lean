import Dubon2026.GaussianTestPairing
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # Bounded continuous density of an actual finite planar measure

The density is the inverse characteristic integral. Its identity with the
original measure is proved by the Gaussian compact-test comparison.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology CompactlySupported

noncomputable section

/-- An integrable planar characteristic function gives the actual continuous density. -/
theorem measure_eq_withDensity_planarCharDensity {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (planarCharDensity μ x)) := by
  letI : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (planarCharDensity μ x))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (continuous_planarCharDensity hμ)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_planarCharDensity hμ).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (planarCharDensity_nonneg hμ _), smul_eq_mul,
    mul_comm (planarCharDensity μ _) (f _)]
  exact (integral_test_planarCharDensity hμ f).symm

theorem planar_measure_le_density_bound {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) {L : ℝ} (hL : ∀ x, planarCharDensity μ x ≤ L)
    {s : Set ℂ} (hs : MeasurableSet s) :
    μ s ≤ ENNReal.ofReal L * volume s := by
  rw [measure_eq_withDensity_planarCharDensity hμ, withDensity_apply _ hs]
  calc
    (∫⁻ x in s, ENNReal.ofReal (planarCharDensity μ x)) ≤ ∫⁻ _x in s, ENNReal.ofReal L :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hL x))
    _ = ENNReal.ofReal L * volume s := by simp

theorem planar_measure_absolutelyContinuous {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) : μ ≪ volume := by
  rw [measure_eq_withDensity_planarCharDensity hμ]
  exact withDensity_absolutelyContinuous _ _

end

end Dubon2026

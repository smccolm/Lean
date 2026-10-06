import Dubon2026.PlanarDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Translation-uniform disk estimates for bounded planar densities -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem planar_closedBall_measure_le {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x, planarCharDensity μ x ≤ L) (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    μ (Metric.closedBall a r) ≤ ENNReal.ofReal (L * Real.pi * r ^ 2) := by
  calc
    μ (Metric.closedBall a r) ≤ ENNReal.ofReal L * volume (Metric.closedBall a r) :=
      planar_measure_le_density_bound hμ hb Metric.isClosed_closedBall.measurableSet
    _ = ENNReal.ofReal (L * Real.pi * r ^ 2) := by
      rw [Complex.volume_closedBall]
      rw [ENNReal.ofReal_mul (mul_nonneg hL Real.pi_pos.le), ENNReal.ofReal_mul hL,
        ENNReal.ofReal_pow hr]
      simp only [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      ring

theorem planar_translated_smallBall {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x, planarCharDensity μ x ≤ L) (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    μ {z : ℂ | ‖a + z‖ ≤ r} ≤ ENNReal.ofReal (L * Real.pi * r ^ 2) := by
  have he : {z : ℂ | ‖a + z‖ ≤ r} = Metric.closedBall (-a) r := by
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add,
      add_comm a z]
  rw [he]
  exact planar_closedBall_measure_le hμ hL hb (-a) hr

theorem planar_measure_singleton {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (a : ℂ) : μ {a} = 0 :=
  planar_measure_absolutelyContinuous hμ (measure_singleton a)

theorem planar_translated_ne_zero_ae {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (a : ℂ) : ∀ᵐ z ∂μ, a + z ≠ 0 := by
  rw [ae_iff]
  have he : {z : ℂ | ¬a + z ≠ 0} = {-a} := by
    ext z
    simp only [Set.mem_setOf_eq, not_not, Set.mem_singleton_iff]
    exact add_eq_zero_iff_eq_neg'
  rw [he]
  exact planar_measure_singleton hμ (-a)

end

end Dubon2026

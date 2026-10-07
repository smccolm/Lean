import Dubon2026.JessenMass
import Dubon2026.ZeroFreeHalfPlanes

/-! # Jessen mass for every nonzero first coefficient

The source mass proposition assumes a₁ ≠ 0, without normalizing its value.
Uniform convergence of the actual Bohr polynomial supplies the limiting value
log |a₁| at the right end; the limiting derivative is still zero.
-/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

theorem tendsto_jessenFunction_atTop_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (jessenFunction a N) atTop (𝓝 (Real.log ‖a 1‖)) := by
  have hg (z : PrimeTorus N) :
      ‖(a 1 • UnitAddTorus.mFourier (primeExponent N 1)) z‖ = ‖a 1‖ := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, norm_mul, norm_mFourier_apply,
      mul_one]
  have h := tendsto_integral_log_of_constant_modulus_limit (norm_pos_iff.mpr ha) hg
    (tendsto_bohrOnTorus_atTop a hN) (integrable_bohrOnTorus_log a N)
  change Tendsto (fun σ => jessenFunction a N σ) atTop _
  simpa only [jessenFunction_eq_haar hN ha, haarLogPotential] using h

theorem tendsto_jessen_derivatives_atTop_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (fun x => derivWithin (jessenFunction a N) (Iio x) x) atTop (𝓝 0) ∧
      Tendsto (fun x => derivWithin (jessenFunction a N) (Ioi x) x) atTop (𝓝 0) := by
  apply tendsto_convex_derivatives_atTop (convexOn_jessenFunction hN ha)
  simpa only [zero_mul, sub_zero] using tendsto_jessenFunction_atTop_nonzero hN ha

theorem tendsto_jessenStieltjes_atTop_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (jessenStieltjes hN ha) atTop (𝓝 0) := by
  change Tendsto (fun x => jessenStieltjes hN ha x) atTop (𝓝 0)
  simpa only [jessenStieltjes_apply] using (tendsto_jessen_derivatives_atTop_nonzero hN ha).2

theorem jessenMeasure_univ_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    jessenMeasure hN ha univ = ENNReal.ofReal (Real.log (lastIndex a N)) := by
  simpa only [jessenMeasure, zero_sub, neg_neg] using
    (jessenStieltjes hN ha).measure_univ (tendsto_jessenStieltjes_atBot hN ha)
      (tendsto_jessenStieltjes_atTop_nonzero hN ha)

theorem jessenMeasure_finite_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : IsFiniteMeasure (jessenMeasure hN ha) :=
  ⟨by rw [jessenMeasure_univ_nonzero hN ha]; exact ENNReal.ofReal_lt_top⟩

theorem scaledJessenMeasure_univ_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    scaledJessenMeasure hN ha univ =
      ENNReal.ofReal (Real.log (lastIndex a N) / (2 * Real.pi)) := by
  rw [scaledJessenMeasure, Measure.smul_apply, smul_eq_mul, jessenMeasure_univ_nonzero hN ha,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  congr 1
  ring

theorem normalizedJessenMeasure_isProbability_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (hM : 1 < lastIndex a N) :
    IsProbabilityMeasure (normalizedJessenMeasure hN ha) := by
  have hlog : 0 < Real.log (lastIndex a N) := Real.log_pos (by exact_mod_cast hM)
  constructor
  rw [normalizedJessenMeasure, Measure.smul_apply, smul_eq_mul, jessenMeasure_univ_nonzero hN ha]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hlog)) ENNReal.ofReal_ne_top

theorem jessenMeasure_zero_of_lastIndex_one_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (hM : lastIndex a N = 1) : jessenMeasure hN ha = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [jessenMeasure_univ_nonzero hN ha, hM, Nat.cast_one, Real.log_one, ENNReal.ofReal_zero]

end Dubon2026

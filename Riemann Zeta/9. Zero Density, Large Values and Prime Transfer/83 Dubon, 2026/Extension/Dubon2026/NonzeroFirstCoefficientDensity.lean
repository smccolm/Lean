import Dubon2026.CoefficientScaling
import Dubon2026.GeneralZeroDensity

/-! # Jessen–Tornehave for every nonzero first coefficient

Normalize the actual polynomial by its first coefficient. The proved scalar
identities preserve each finite-height multiplicity-weighted count and the
Jessen derivative measure, including all vertical boundary atoms.
-/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_zeroDensity_jessenMeasure_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T)) atTop
      (𝓝 ((jessenMeasure hN ha (Ioo l u)).toReal / (2 * Real.pi))) := by
  have hb : (a 1)⁻¹ * a 1 = 1 := inv_mul_cancel₀ ha
  simpa only [verticalZeroCount_scale hN ha (inv_ne_zero ha),
    jessenMeasure_scale hN ha (inv_ne_zero ha)] using
      tendsto_zeroDensity_jessenMeasure (a := fun n => (a 1)⁻¹ * a n) hN hb l u

theorem tendsto_zeroDensity_one_sided_derivatives_nonzero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l < u) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T)) atTop
      (𝓝 ((derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / (2 * Real.pi))) := by
  have hb : (a 1)⁻¹ * a 1 = 1 := inv_mul_cancel₀ ha
  simpa only [verticalZeroCount_scale hN ha (inv_ne_zero ha),
    derivWithin_jessenFunction_scale hN ha (inv_ne_zero ha)] using
      tendsto_zeroDensity_one_sided_derivatives (a := fun n => (a 1)⁻¹ * a n) hN hb hlu

end Dubon2026

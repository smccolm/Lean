import Dubon2026.JessenAtomRegularity
import Dubon2026.ContinuousEndpointZeroDensity

/-! # The actual Jessen–Tornehave interval formula when the boundary carries no atoms -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

theorem tendsto_zeroDensity_atom_free {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u : ℝ} (hlu : l ≤ u)
    (hl : jessenMeasure hN (ha.trans_ne one_ne_zero) {l} = 0)
    (hu : jessenMeasure hN (ha.trans_ne one_ne_zero) {u} = 0) :
    Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop
        (𝓝 ((jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo l u)).toReal / (2 * Real.pi))) := by
  rcases hlu.eq_or_lt with he | hlt
  · subst u
    simp only [verticalZeroCount_empty_interval hN (ha.trans_ne one_ne_zero) le_rfl,
      Nat.cast_zero, zero_div, Ioo_self, measure_empty, ENNReal.toReal_zero]
    exact tendsto_const_nhds
  have hdl := hasDerivAt_jessen_of_atom_eq_zero hN (ha.trans_ne one_ne_zero) hl
  have hdu := hasDerivAt_jessen_of_atom_eq_zero hN (ha.trans_ne one_ne_zero) hu
  have hdif : 0 ≤ derivWithin (jessenFunction a N) (Ioi u) u -
      derivWithin (jessenFunction a N) (Ioi l) l :=
    sub_nonneg.mpr (monotone_convex_rightDeriv (convexOn_jessenFunction hN
      (ha.trans_ne one_ne_zero)) hlt.le)
  rw [jessenMeasure_Ioo,
    hdu.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio u), ENNReal.toReal_ofReal hdif]
  exact tendsto_zeroDensity_differentiable_endpoints hN ha hlt hdl hdu

end Dubon2026

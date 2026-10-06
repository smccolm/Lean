import Dubon2026.JessenConvexity
import Dubon2026.ConvexDerivatives

/-! # The positive Stieltjes measure associated with the actual Jessen function

This constructs the convex derivative measure and its exact endpoint formulas.
The separate identification with multiplicity-weighted vertical zero counts is
not asserted by this module.
-/

namespace Dubon2026

open Set MeasureTheory Function

noncomputable section

/-- The right derivative of the actual fixed-length Jessen function as a Stieltjes function. -/
def jessenStieltjes {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    StieltjesFunction ℝ :=
  convexDerivativeStieltjes (convexOn_jessenFunction hN ha)

/-- The positive second-derivative measure before zero-frequency or probability scaling. -/
def jessenMeasure {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) : Measure ℝ :=
  (jessenStieltjes hN ha).measure

instance jessenMeasure_isLocallyFinite {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : IsLocallyFiniteMeasure (jessenMeasure hN ha) :=
  inferInstanceAs (IsLocallyFiniteMeasure (jessenStieltjes hN ha).measure)

theorem jessenStieltjes_apply {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ) :
    jessenStieltjes hN ha x = derivWithin (jessenFunction a N) (Ioi x) x :=
  convexDerivativeStieltjes_apply _ _

theorem leftLim_jessenStieltjes {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ) :
    leftLim (jessenStieltjes hN ha) x = derivWithin (jessenFunction a N) (Iio x) x :=
  leftLim_convexDerivativeStieltjes _ _

theorem jessenMeasure_Ioo {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    jessenMeasure hN ha (Ioo l u) = ENNReal.ofReal
      (derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) :=
  convexDerivativeStieltjes_measure_Ioo _ _ _

theorem jessenMeasure_Ioc {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    jessenMeasure hN ha (Ioc l u) = ENNReal.ofReal
      (derivWithin (jessenFunction a N) (Ioi u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) := by
  rw [jessenMeasure, StieltjesFunction.measure_Ioc, jessenStieltjes_apply,
    jessenStieltjes_apply]

theorem jessenMeasure_singleton {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ) :
    jessenMeasure hN ha {x} = ENNReal.ofReal
      (derivWithin (jessenFunction a N) (Ioi x) x -
        derivWithin (jessenFunction a N) (Iio x) x) := by
  rw [jessenMeasure, StieltjesFunction.measure_singleton, jessenStieltjes_apply,
    leftLim_jessenStieltjes]

end

end Dubon2026

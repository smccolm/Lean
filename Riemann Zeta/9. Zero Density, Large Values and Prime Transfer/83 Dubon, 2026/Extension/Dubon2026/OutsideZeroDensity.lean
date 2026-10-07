import Dubon2026.TotalZeroDensity
import Dubon2026.AtomFreeZeroDensity
import Dubon2026.ConcentrationTails

/-! # Actual outside-band zero densities at atom-free boundary lines -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

theorem tendsto_outsideVerticalZeroDensity {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {α ε : ℝ} (hε : 0 ≤ ε)
    (hl : jessenMeasure hN (ha.trans_ne one_ne_zero) {α - ε} = 0)
    (hu : jessenMeasure hN (ha.trans_ne one_ne_zero) {α + ε} = 0) :
    Tendsto (fun T => (outsideVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) α ε T : ℝ) /
      (2 * T)) atTop (𝓝 ((Real.log (lastIndex a N) -
        (jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo (α - ε) (α + ε))).toReal) /
          (2 * Real.pi))) := by
  have hi := tendsto_zeroDensity_atom_free hN ha (show α - ε ≤ α + ε by linarith) hl hu
  have ht := tendsto_totalVerticalZeroDensity hN ha
  have he (T : ℝ) :
      (outsideVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) α ε T : ℝ) =
        (totalVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) T : ℝ) -
          (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) (α - ε) (α + ε) T : ℝ) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ))
      (outsideVerticalZeroCount_add_inside hN (ha.trans_ne one_ne_zero) α ε T)
    push_cast at hh
    linarith
  simpa only [he, sub_div] using ht.sub hi

theorem jessenProbability_outside_toReal {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) (α ε : ℝ) :
    ((jessenProbability ha N : Measure ℝ) {x | ε ≤ |x - α|}).toReal =
      (Real.log (lastIndex a N) -
        (jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo (α - ε) (α + ε))).toReal) /
          Real.log (lastIndex a N) := by
  have hlog : 0 < Real.log (lastIndex a N) := Real.log_pos (by exact_mod_cast hM)
  rw [outside_eq_compl_Ioo, measure_compl measurableSet_Ioo (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_one, jessenProbability_eq ha hN hM, normalizedJessenMeasure,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hlog.le]
  field_simp

theorem tendsto_normalized_outsideVerticalZeroDensity {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) {α ε : ℝ} (hε : 0 ≤ ε)
    (hl : jessenMeasure hN (ha.trans_ne one_ne_zero) {α - ε} = 0)
    (hu : jessenMeasure hN (ha.trans_ne one_ne_zero) {α + ε} = 0) :
    Tendsto (fun T => (2 * Real.pi / Real.log (lastIndex a N)) *
      ((outsideVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) α ε T : ℝ) / (2 * T)))
        atTop (𝓝 (((jessenProbability ha N : Measure ℝ) {x | ε ≤ |x - α|}).toReal)) := by
  have h := (tendsto_outsideVerticalZeroDensity hN ha hε hl hu).const_mul
    (2 * Real.pi / Real.log (lastIndex a N))
  rw [jessenProbability_outside_toReal hN ha hM]
  convert h using 1
  field_simp

end Dubon2026

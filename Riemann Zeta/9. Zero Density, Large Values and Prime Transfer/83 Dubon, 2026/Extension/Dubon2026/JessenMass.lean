import Dubon2026.JessenLeftLimit

/-! # Total mass and probability normalization of the Jessen derivative measure

All masses come from the proved terminal affine asymptote and right-end limit.
Identification with actual vertical zero counts remains a separate theorem.
-/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

theorem jessenMeasure_univ {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 = 1) :
    jessenMeasure hN (ha.trans_ne one_ne_zero) univ = ENNReal.ofReal (Real.log (lastIndex a N)) := by
  simpa only [jessenMeasure, zero_sub, neg_neg] using
    (jessenStieltjes hN (ha.trans_ne one_ne_zero)).measure_univ
      (tendsto_jessenStieltjes_atBot hN (ha.trans_ne one_ne_zero))
      (tendsto_jessenStieltjes_atTop hN ha)

instance jessenMeasure_isFinite {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    IsFiniteMeasure (jessenMeasure hN (ha.trans_ne one_ne_zero)) :=
  ⟨by rw [jessenMeasure_univ hN ha]; exact ENNReal.ofReal_lt_top⟩

theorem jessenMeasure_Iic {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ) :
    jessenMeasure hN ha (Iic x) = ENNReal.ofReal
      (derivWithin (jessenFunction a N) (Ioi x) x + Real.log (lastIndex a N)) := by
  rw [jessenMeasure, StieltjesFunction.measure_Iic _ (tendsto_jessenStieltjes_atBot hN ha),
    jessenStieltjes_apply, sub_neg_eq_add]

/-- The source's `1/(2π)` scaling of the actual Jessen derivative measure. -/
def scaledJessenMeasure {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • jessenMeasure hN ha

theorem scaledJessenMeasure_univ {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    scaledJessenMeasure hN (ha.trans_ne one_ne_zero) univ =
      ENNReal.ofReal (Real.log (lastIndex a N) / (2 * Real.pi)) := by
  rw [scaledJessenMeasure, Measure.smul_apply, smul_eq_mul, jessenMeasure_univ hN ha,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  congr 1
  ring

/-- Probability scaling by the actual supported length, not the nominal truncation length. -/
def normalizedJessenMeasure {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) : Measure ℝ :=
  (ENNReal.ofReal (Real.log (lastIndex a N)))⁻¹ • jessenMeasure hN ha

theorem normalizedJessenMeasure_univ {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) :
    normalizedJessenMeasure hN (ha.trans_ne one_ne_zero) univ = 1 := by
  have hlog : 0 < Real.log (lastIndex a N) := Real.log_pos (by exact_mod_cast hM)
  rw [normalizedJessenMeasure, Measure.smul_apply, smul_eq_mul, jessenMeasure_univ hN ha]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hlog)) ENNReal.ofReal_ne_top

theorem normalizedJessenMeasure_isProbability {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) :
    IsProbabilityMeasure (normalizedJessenMeasure hN (ha.trans_ne one_ne_zero)) :=
  ⟨normalizedJessenMeasure_univ hN ha hM⟩

theorem jessenMeasure_eq_zero_of_lastIndex_one {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : lastIndex a N = 1) :
    jessenMeasure hN (ha.trans_ne one_ne_zero) = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [jessenMeasure_univ hN ha, hM, Nat.cast_one, Real.log_one, ENNReal.ofReal_zero]

end

end Dubon2026

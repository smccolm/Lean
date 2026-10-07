import Dubon2026.GeneralZeroDensity
import Dubon2026.ZetaZeroCount

/-! # Exact outside-band densities and nested zeta concentration at every radius -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

theorem tendsto_outsideVerticalZeroDensity_all_endpoints {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (α ε : ℝ) :
    Tendsto (fun T => (outsideVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) α ε T : ℝ) /
      (2 * T)) atTop (𝓝 ((Real.log (lastIndex a N) -
        (jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo (α - ε) (α + ε))).toReal) /
          (2 * Real.pi))) := by
  have hi := tendsto_zeroDensity_jessenMeasure hN ha (α - ε) (α + ε)
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

theorem tendsto_normalized_outsideVerticalZeroDensity_all_endpoints {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) (α ε : ℝ) :
    Tendsto (fun T => (2 * Real.pi / Real.log (lastIndex a N)) *
      ((outsideVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) α ε T : ℝ) / (2 * T)))
        atTop (𝓝 (((jessenProbability ha N : Measure ℝ) {x | ε ≤ |x - α|}).toReal)) := by
  have h := (tendsto_outsideVerticalZeroDensity_all_endpoints hN ha α ε).const_mul
    (2 * Real.pi / Real.log (lastIndex a N))
  rw [jessenProbability_outside_toReal hN ha hM]
  convert h using 1
  field_simp

theorem zeta_outside_count_limit_all_endpoints {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    Tendsto (fun T => (outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega)
      one_ne_zero (1 / 2) ε T : ℝ) / (2 * T)) atTop
        (𝓝 ((Real.log N / (2 * Real.pi)) *
          ((jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ)
            {x | ε ≤ |x - 1 / 2|}).toReal)) := by
  have hn : 1 ≤ N := by omega
  have hm : 1 < lastIndex (fun _ => (1 : ℂ)) N := by rw [zeta_lastIndex hn]; omega
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht := tendsto_outsideVerticalZeroDensity_all_endpoints hn (a := fun _ => (1 : ℂ)) rfl
    (1 / 2) ε
  rw [jessenProbability_outside_toReal hn rfl hm, zeta_lastIndex hn]
  convert ht using 1
  rw [zeta_lastIndex hn]
  field_simp

/-- First the genuine height limit at fixed length, then the length limit; no
exceptional boundary radius is required. -/
theorem zeta_zero_count_concentration_all_endpoints {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ → ℝ,
      (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
        (outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega) one_ne_zero
          (1 / 2) ε T : ℝ) / (2 * T)) atTop (𝓝 (D N))) ∧
      Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  let D : ℕ → ℝ := fun N => (Real.log N / (2 * Real.pi)) *
    ((jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {x | ε ≤ |x - 1 / 2|}).toReal
  refine ⟨D, fun N hN => zeta_outside_count_limit_all_endpoints hN ε, ?_⟩
  have hh := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ∞)).comp
    (zeta_jessen_concentration.2.2.2.2 ε hε)
  simp only [ENNReal.toReal_zero, Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  dsimp only [D]
  field_simp
  simp only [mul_comm]

end

end Dubon2026

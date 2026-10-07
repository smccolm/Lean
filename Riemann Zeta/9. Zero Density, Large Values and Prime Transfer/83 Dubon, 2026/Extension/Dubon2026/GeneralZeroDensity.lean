import Dubon2026.InnerCountConvergence
import Dubon2026.AtomFreeZeroDensity
import Dubon2026.BoundaryAtoms
import Mathlib.Topology.Order.IsLUB

/-! # The actual Jessen–Tornehave open-strip formula at arbitrary endpoints -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- Exhaustion from inside identifies the Haar mean without discarding vertical
boundary atoms or assuming the desired zero-frequency formula. -/
theorem integral_twistZeroCount_eq_jessenMeasure {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    (∫ z, (twistZeroCount a N hN (ha.trans_ne one_ne_zero) l u 1 z : ℝ) ∂torusHaar N) / 2 =
      (jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo l u)).toReal / (2 * Real.pi) := by
  by_cases hlu : l < u
  · let μ := jessenMeasure hN (ha.trans_ne one_ne_zero)
    letI : IsFiniteMeasure μ := jessenMeasure_isFinite hN ha
    have hd : Dense {x : ℝ | μ {x} = 0} := by
      simpa only [compl_setOf, not_not] using (countable_measure_atoms μ).dense_compl ℝ
    obtain ⟨L, hmL, hiL, htL⟩ := hd.exists_seq_strictAnti_tendsto_of_lt
      (show l < (l + u) / 2 by linarith)
    obtain ⟨U, hmU, hiU, htU⟩ := hd.exists_seq_strictMono_tendsto_of_lt
      (show (l + u) / 2 < u by linarith)
    have hL (n : ℕ) : l ≤ L n := (hiL n).1.1.le
    have hU (n : ℕ) : U n ≤ u := (hiU n).1.2.le
    have he (n : ℕ) :
        (∫ z, (twistZeroCount a N hN (ha.trans_ne one_ne_zero) (L n) (U n) 1 z : ℝ)
          ∂torusHaar N) / 2 = (μ (Ioo (L n) (U n))).toReal / (2 * Real.pi) :=
      tendsto_nhds_unique (tendsto_zeroDensity_torus_mean hN (ha.trans_ne one_ne_zero) (L n) (U n))
        (tendsto_zeroDensity_atom_free hN ha ((hiL n).1.2.trans (hiU n).1.1).le
          (hiL n).2 (hiU n).2)
    have hc := (tendsto_integral_twistZeroCount_inner hN (ha.trans_ne one_ne_zero)
      hL hU htL htU 1).div_const 2
    have hm := ((ENNReal.tendsto_toReal (measure_ne_top μ (Ioo l u))).comp
      (tendsto_measure_inner_open_intervals μ hmL.antitone hmU.monotone hL hU htL htU)).div_const
        (2 * Real.pi)
    exact tendsto_nhds_unique hc (hm.congr fun n => (he n).symm)
  · have he : twistZeroCount a N hN (ha.trans_ne one_ne_zero) l u 1 = fun _ => 0 := by
      funext z
      exact verticalZeroCount_empty_interval hN (by rw [twistedCoefficients_one]; exact ha.trans_ne one_ne_zero) (le_of_not_gt hlu) 1
    simp only [he, Nat.cast_zero, integral_zero, zero_div, Ioo_eq_empty_of_le (le_of_not_gt hlu),
      measure_empty, ENNReal.toReal_zero]

/-- Multiplicity-weighted zero frequency equals the actual Jessen measure on every
open strip, including arbitrary atom-carrying endpoints. -/
theorem tendsto_zeroDensity_jessenMeasure {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (l u : ℝ) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop
      (𝓝 ((jessenMeasure hN (ha.trans_ne one_ne_zero) (Ioo l u)).toReal / (2 * Real.pi))) := by
  rw [← integral_twistZeroCount_eq_jessenMeasure hN ha l u]
  exact tendsto_zeroDensity_torus_mean hN (ha.trans_ne one_ne_zero) l u

/-- The exact source convention is the left derivative at the upper endpoint
minus the right derivative at the lower endpoint. -/
theorem tendsto_zeroDensity_one_sided_derivatives {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u : ℝ} (hlu : l < u) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop (𝓝 ((derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / (2 * Real.pi))) := by
  have hf := convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  have hn : 0 ≤ derivWithin (jessenFunction a N) (Iio u) u -
      derivWithin (jessenFunction a N) (Ioi l) l :=
    sub_nonneg.mpr ((hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ _) hlu).trans
      (hf.slope_le_leftDeriv_of_mem_interior (mem_univ _) (by simp) hlu))
  have hh := tendsto_zeroDensity_jessenMeasure hN ha l u
  rwa [jessenMeasure_Ioo, ENNReal.toReal_ofReal hn] at hh

end

end Dubon2026

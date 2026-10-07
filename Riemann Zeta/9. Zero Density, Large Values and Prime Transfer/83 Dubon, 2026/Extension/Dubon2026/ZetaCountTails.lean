import Dubon2026.ZetaZeroCount
import Dubon2026.ZeroCountRadius

/-! # Iterated eventual smallness of the literal zero count for every band radius

This additionally avoids the boundary restriction for the quantified tail bound.
It does not assert existence of a fixed-length limit on an atom-carrying boundary.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology ENNReal

theorem zeta_outside_count_eventually_small {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ hN : 2 ≤ N, ∀ᶠ T : ℝ in atTop,
      (2 * Real.pi / Real.log N) *
        ((outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega) one_ne_zero
          (1 / 2) ε T : ℝ) / (2 * T)) < δ := by
  let μ : ℕ → Measure ℝ := fun N => jessenProbability (a := fun _ => (1 : ℂ)) rfl N
  obtain ⟨η, hη, hatom⟩ := exists_atom_free_radius μ (1 / 2) hε
  have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
    (zeta_jessen_concentration.2.2.2.2 η hη.1)
  simp only [ENNReal.toReal_zero, Function.comp_def] at hh
  have hsmall : ∀ᶠ N : ℕ in atTop, (μ N {x | η ≤ |x - 1 / 2|}).toReal < δ :=
    hh (Iio_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with N hN hs
  refine ⟨hN, ?_⟩
  have hn : 1 ≤ N := by omega
  have hm : 1 < lastIndex (fun _ => (1 : ℂ)) N := by rw [zeta_lastIndex hn]; omega
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht := tendsto_normalized_outsideVerticalZeroDensity hn (a := fun _ => (1 : ℂ))
    rfl hm hη.1.le
      (jessenMeasure_atom_eq_zero_of_probability hn rfl hm (hatom N).1)
      (jessenMeasure_atom_eq_zero_of_probability hn rfl hm (hatom N).2)
  rw [zeta_lastIndex hn] at ht
  have hsT := ht (Iio_mem_nhds hs)
  filter_upwards [hsT, eventually_ge_atTop (1 : ℝ)] with T hT hTpos
  apply lt_of_le_of_lt ?_ hT
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply div_le_div_of_nonneg_right ?_ (by linarith)
  exact_mod_cast outsideVerticalZeroCount_mono_radius hn (a := fun _ => (1 : ℂ))
    one_ne_zero (1 / 2) T hη.2.le

end Dubon2026

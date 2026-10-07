import Dubon2026.ZetaApplication
import Dubon2026.OutsideZeroDensity
import Dubon2026.BoundaryAtoms

/-! # Critical-line concentration of actual zeta-truncation zero counts

The fixed-length height limit is proved before the length tends to infinity.
The source's convention excludes boundary lines carrying a Jessen atom; the
exceptional radii are proved countable simultaneously for every length.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology ENNReal

theorem zeta_outside_count_limit {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (hl : (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 - ε} = 0)
    (hu : (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 + ε} = 0) :
    Tendsto (fun T => (outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega)
      one_ne_zero (1 / 2) ε T : ℝ) / (2 * T)) atTop
        (𝓝 ((Real.log N / (2 * Real.pi)) *
          ((jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ)
            {x | ε ≤ |x - 1 / 2|}).toReal)) := by
  have hn : 1 ≤ N := by omega
  have hm : 1 < lastIndex (fun _ => (1 : ℂ)) N := by rw [zeta_lastIndex hn]; omega
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht := tendsto_outsideVerticalZeroDensity hn (a := fun _ => (1 : ℂ)) rfl hε
    (jessenMeasure_atom_eq_zero_of_probability hn rfl hm hl)
    (jessenMeasure_atom_eq_zero_of_probability hn rfl hm hu)
  rw [jessenProbability_outside_toReal hn rfl hm, zeta_lastIndex hn]
  convert ht using 1
  rw [zeta_lastIndex hn]
  field_simp

/-- The direct nested-limit formulation, with the source's explicit atom-free boundaries. -/
theorem zeta_zero_count_concentration {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ N : ℕ, 2 ≤ N →
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 - ε} = 0 ∧
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {1 / 2 + ε} = 0) :
    ∃ D : ℕ → ℝ,
      (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
        (outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega) one_ne_zero
          (1 / 2) ε T : ℝ) / (2 * T)) atTop (𝓝 (D N))) ∧
      Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  let D : ℕ → ℝ := fun N => (Real.log N / (2 * Real.pi)) *
    ((jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) {x | ε ≤ |x - 1 / 2|}).toReal
  refine ⟨D, fun N hN => zeta_outside_count_limit hN hε.le (hb N hN).1 (hb N hN).2, ?_⟩
  have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
    (zeta_jessen_concentration.2.2.2.2 ε hε)
  simp only [ENNReal.toReal_zero, Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  dsimp only [D]
  field_simp
  simp only [mul_comm]

/-- One countable exception set implements the boundary convention for every truncation. -/
theorem zeta_zero_count_concentration_off_countable :
    ∃ B : Set ℝ, B.Countable ∧ ∀ ε : ℝ, 0 < ε → ε ∉ B →
      ∃ D : ℕ → ℝ,
        (∀ (N : ℕ) (hN : 2 ≤ N), Tendsto (fun T =>
          (outsideVerticalZeroCount (fun _ => (1 : ℂ)) N (by omega) one_ne_zero
            (1 / 2) ε T : ℝ) / (2 * T)) atTop (𝓝 (D N))) ∧
        Tendsto (fun N : ℕ => (2 * Real.pi / Real.log N) * D N) atTop (𝓝 0) := by
  let μ : ℕ → Measure ℝ := fun N => jessenProbability (a := fun _ => (1 : ℂ)) rfl N
  let B : Set ℝ := {ε | ∃ N, 2 ≤ N ∧ (μ N {1 / 2 - ε} ≠ 0 ∨ μ N {1 / 2 + ε} ≠ 0)}
  have hc : B.Countable := by
    apply (countable_boundary_atom_radii μ (1 / 2)).mono
    rintro ε ⟨N, _, h⟩
    exact ⟨N, h⟩
  refine ⟨B, hc, fun ε hε hb => ?_⟩
  apply zeta_zero_count_concentration hε
  intro N hN
  constructor
  · by_contra h
    exact hb ⟨N, hN, Or.inl h⟩
  · by_contra h
    exact hb ⟨N, hN, Or.inr h⟩

end Dubon2026

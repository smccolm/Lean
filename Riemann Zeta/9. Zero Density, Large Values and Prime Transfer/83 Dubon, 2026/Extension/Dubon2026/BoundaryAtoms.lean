import Dubon2026.JessenProbability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! # The source's convention of avoiding atom-carrying boundary lines -/

namespace Dubon2026

open MeasureTheory Set Function

/-- A finite measure has only countably many points of nonzero mass. -/
theorem countable_measure_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    {x : ℝ | μ {x} ≠ 0}.Countable := by
  simpa only [id_eq, setOf_eq_eq_singleton, pos_iff_ne_zero] using
    (Measure.countable_meas_level_set_pos (μ := μ) measurable_id)

theorem countable_boundary_atom_radii (μ : ℕ → Measure ℝ)
    [∀ N, IsFiniteMeasure (μ N)] (α : ℝ) :
    {ε : ℝ | ∃ N, μ N {α - ε} ≠ 0 ∨ μ N {α + ε} ≠ 0}.Countable := by
  have hleft (N : ℕ) := (countable_measure_atoms (μ N)).image (fun x => α - x)
  have hright (N : ℕ) := (countable_measure_atoms (μ N)).image (fun x => x - α)
  apply (countable_iUnion fun N => (hleft N).union (hright N)).mono
  rintro ε ⟨N, h | h⟩
  · exact mem_iUnion.mpr ⟨N, Or.inl ⟨α - ε, h, by ring⟩⟩
  · exact mem_iUnion.mpr ⟨N, Or.inr ⟨α + ε, h, by ring⟩⟩

theorem exists_atom_free_radius (μ : ℕ → Measure ℝ)
    [∀ N, IsFiniteMeasure (μ N)] (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η ∈ Ioo 0 ε, ∀ N, μ N {α - η} = 0 ∧ μ N {α + η} = 0 := by
  obtain ⟨η, hη, hn⟩ := (countable_boundary_atom_radii μ α).dense_compl ℝ
    |>.inter_open_nonempty (Ioo 0 ε) isOpen_Ioo (nonempty_Ioo.mpr hε)
  refine ⟨η, hη, fun N => ?_⟩
  constructor
  · by_contra h
    exact hn ⟨N, Or.inl h⟩
  · by_contra h
    exact hn ⟨N, Or.inr h⟩

theorem jessenMeasure_atom_eq_zero_of_probability {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) {x : ℝ}
    (hx : (jessenProbability ha N : Measure ℝ) {x} = 0) :
    jessenMeasure hN (ha.trans_ne one_ne_zero) {x} = 0 := by
  rw [jessenProbability_eq ha hN hM, normalizedJessenMeasure, Measure.smul_apply,
    smul_eq_mul] at hx
  exact (mul_eq_zero.mp hx).resolve_left (by simp)

end Dubon2026

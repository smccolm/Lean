import Mathlib
import RiemannZeta.GuthMaynard.ExtractSeparated

open Finset

namespace RiemannZeta.GuthMaynard

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (M : ℕ) :
    (zeroCountRect model σ 1 T (T + M) : ℝ) ≤ ∑ k ∈ Finset.range M, (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h_split := zeroCountRect_split model σ 1 T (T + M) (T + M + 1)
    have eq1 : T + ↑(M + 1) = T + ↑M + 1 := by push_cast; ring
    rw [eq1]
    have h_cast : (zeroCountRect model σ 1 T (T + ↑M + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ↑M) : ℝ) + (zeroCountRect model σ 1 (T + ↑M) (T + ↑M + 1) : ℝ) := by exact_mod_cast h_split
    linarith

theorem representative_selection (model : ZetaZeroCountModel) (hLocal : LocalZeroCountHypothesis model) : RepresentativeSelectionHypothesis model := by
  intro σ T hT
  have ⟨C, hC_pos, hLocal_bound⟩ := hLocal
  let S := (Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))
  use S
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨k, hk, rfl⟩
    constructor
    · linarith [Nat.cast_nonneg k]
    · have h1 : (k : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast Nat.le_of_lt_succ hk
      have h2 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
      linarith
  · intro x
    by_cases h_empty : (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card = 0
    · linarith
    · have h_pos : 0 < (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card := by omega
      -- there is at least one element. If there are two elements, their difference is an integer.
      sorry
  · sorry

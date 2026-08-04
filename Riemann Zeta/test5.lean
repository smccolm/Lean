import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ExtractSeparated

open Complex
open Finset

namespace RiemannZeta.GuthMaynard

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (M : ℕ) :
    (zeroCountRect model σ 1 T (T + M + 1) : ℝ) ≤ ∑ k ∈ Finset.range (M + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction M with
  | zero =>
    simp only [Nat.zero_eq, Nat.cast_zero, add_zero, Finset.range_one, Finset.sum_singleton, le_refl]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h_split := zeroCountRect_split model σ 1 T (T + (M : ℝ) + 1) (T + (M + 1 : ℝ) + 1)
    have h_cast : (zeroCountRect model σ 1 T (T + (M + 1 : ℝ) + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + (M : ℝ) + 1) : ℝ) + (zeroCountRect model σ 1 (T + (M : ℝ) + 1) (T + (M + 1 : ℝ) + 1) : ℝ) := by exact_mod_cast h_split
    linarith

theorem representative_selection (model : ZetaZeroCountModel) (hLocal : LocalZeroCountHypothesis model) : RepresentativeSelectionHypothesis model := by
  intro σ T hT
  have ⟨C, hC_pos, hLocal_bound⟩ := hLocal
  let S := (Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))
  use S
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [S, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨k, hk, rfl⟩
    constructor
    · linarith [Nat.cast_nonneg k]
    · have h1 : (k : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast Nat.le_of_lt_succ hk
      have h2 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
      linarith
  · intro x
    have h_card : (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ 1 := by
      sorry
    linarith
  · use C
    refine ⟨hC_pos, ?_⟩
    sorry

end RiemannZeta.GuthMaynard

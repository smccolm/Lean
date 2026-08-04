import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ExtractSeparated

open Complex
open Finset

namespace RiemannZeta.GuthMaynard

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (N : ℕ) :
    (zeroCountRect model σ 1 T (T + N) : ℝ) ≤ ∑ k ∈ Finset.range N, (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction N with
  | zero =>
    simp [zeroCountRect, zerosInRect, Finset.sum_empty]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h_split := zeroCountRect_split model σ 1 T (T + N) (T + (N + 1 : ℕ))
    have h_cast : (zeroCountRect model σ 1 T (T + (N + 1 : ℕ)) : ℝ) ≤ (zeroCountRect model σ 1 T (T + N) : ℝ) + (zeroCountRect model σ 1 (T + N) (T + (N + 1 : ℕ)) : ℝ) := by exact_mod_cast h_split
    have h_eq : T + (N + 1 : ℕ) = (T + N) + 1 := by push_cast; ring
    rw [h_eq] at h_cast
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
    sorry
  · use C
    refine ⟨hC_pos, ?_⟩
    sorry

end RiemannZeta.GuthMaynard

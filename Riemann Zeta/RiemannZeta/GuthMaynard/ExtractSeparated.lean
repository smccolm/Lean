import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated

open Complex
open Finset

namespace RiemannZeta.GuthMaynard

/--
The classical local zero-density estimate:
The number of zeros in a unit interval [t, t+1] is bounded by O(log T)
for t ∈ [T, 2T].
-/
def LocalZeroCountHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∃ C > 0, ∀ (σ t T : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
    (zeroCountRect model σ 1 t (t + 1) : ℝ) ≤ C * Real.log T

/--
F-05: Extract separated ordinates.
For any `T ≥ 2` and `σ`, there exists a 1-separated set `W ⊂ [T, 2T]`
whose cardinality controls the number of relevant zeros in the dyadic slab.
-/
def ExtractSeparatedHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), T ≥ 2 →
    ∃ (W : Finset ℝ), IsSeparated 1 W ∧ InTargetInterval T W ∧
      ∃ C > 0, (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (W.card : ℝ) * Real.log T

/--
Intermediate combinatorial geometric hypothesis:
We can choose a set of representative ordinates `S` in `[T, 2T]` such that
there is at most 2 points per unit interval, and the total number of zeros
is bounded by `S.card` times the max local zero count.
-/
def RepresentativeSelectionHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), T ≥ 2 →
    ∃ (S : Finset ℝ),
      (∀ x ∈ S, x ∈ Set.Icc T (2 * T)) ∧
      (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ 2) ∧
      (∃ C > 0, (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (S.card : ℝ) * Real.log T)

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (M : ℕ) :
    (zeroCountRect model σ 1 T (T + M + 1) : ℝ) ≤ ∑ k ∈ Finset.range (M + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_one]
    have eq_T2 : T + ↑(0 : ℕ) = T := by push_cast; ring
    rw [eq_T2]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have eq_T1 : T + ↑(M + 1) + 1 = T + M + 1 + 1 := by push_cast; ring
    have eq_T2 : T + ↑(M + 1) = T + M + 1 := by push_cast; ring
    rw [eq_T1, eq_T2]
    have h_split := zeroCountRect_split model σ 1 T (T + M + 1) (T + M + 1 + 1)
    have h_cast : (zeroCountRect model σ 1 T (T + M + 1 + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + M + 1) : ℝ) + (zeroCountRect model σ 1 (T + M + 1) (T + M + 1 + 1) : ℝ) := by
      exact_mod_cast h_split
    linarith

theorem representative_selection (model : ZetaZeroCountModel) (hLocal : LocalZeroCountHypothesis model) : RepresentativeSelectionHypothesis model := by
  intro σ T hT
  have ⟨C, hC_pos, hLocal_bound⟩ := hLocal
  use (Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    simp only [Set.mem_Icc]
    constructor
    · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith [hk0]
    · have h1 : (k : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast Nat.le_of_lt_succ hk
      have h2 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
      linarith
  · intro x
    have h_card : (((Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))).filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro (a : ℝ) ha (b : ℝ) hb
      rw [Finset.mem_filter, Finset.mem_image] at ha
      rw [Finset.mem_filter, Finset.mem_image] at hb
      rcases ha with ⟨⟨ka, hka, rfl⟩, ⟨hax, hax2⟩⟩
      rcases hb with ⟨⟨kb, hkb, rfl⟩, ⟨hbx, hbx2⟩⟩
      have h1 : (ka : ℝ) < (kb : ℝ) + 1 := by linarith
      have h2 : (kb : ℝ) < (ka : ℝ) + 1 := by linarith
      have h1_nat : ka < kb + 1 := by exact_mod_cast h1
      have h2_nat : kb < ka + 1 := by exact_mod_cast h2
      have h_eq : ka = kb := by omega
      congr
    omega
  · use C
    refine ⟨hC_pos, ?_⟩
    have h_split := sum_zeroCountRect_bound model σ T ⌊T⌋₊
    have h_bound : ∑ k ∈ Finset.range (⌊T⌋₊ + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) ≤ ∑ k ∈ Finset.range (⌊T⌋₊ + 1), C * Real.log T := by
      apply Finset.sum_le_sum
      intro k hk
      apply hLocal_bound _ (T + k)
      · exact hT
      · constructor
        · have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith [hk0]
        · have hk2 : (k : ℝ) ≤ ⌊T⌋₊ := by
            rw [Finset.mem_range] at hk
            exact_mod_cast Nat.le_of_lt_succ hk
          have h_T : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
          linarith
    have h_card_S : (((Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))).card : ℝ) = (⌊T⌋₊ + 1 : ℝ) := by
      have h_inj : ∀ a ∈ Finset.range (⌊T⌋₊ + 1), ∀ b ∈ Finset.range (⌊T⌋₊ + 1), T + (a : ℝ) = T + (b : ℝ) → a = b := by
        intro a ha b hb hab
        have h_eq : (a : ℝ) = (b : ℝ) := by linarith
        exact_mod_cast h_eq
      rw [Finset.card_image_of_injOn h_inj]
      rw [Finset.card_range]
      push_cast
      rfl
    have h_sum_simp : ∑ k ∈ Finset.range (⌊T⌋₊ + 1), C * Real.log T = (⌊T⌋₊ + 1 : ℝ) * (C * Real.log T) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rfl
    have h_subset : zerosInRect model σ 1 T (2 * T) ⊆ zerosInRect model σ 1 T (T + ⌊T⌋₊ + 1) := by
      intro s hs
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hs ⊢
      rcases hs with ⟨hs_rect, hs_zero⟩
      refine ⟨?_, hs_zero⟩
      unfold ZeroRectangle at hs_rect ⊢
      rw [Set.mem_setOf_eq] at hs_rect ⊢
      rcases hs_rect with ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, h3, ?_⟩
      have h_floor : (⌊T⌋₊ : ℝ) > T - 1 := Nat.sub_one_lt_floor T
      linarith
    have h_le : (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ⌊T⌋₊ + 1) : ℝ) := by
      unfold zeroCountRect
      have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun x _ _ => Nat.zero_le (model.multiplicity x))
      exact_mod_cast h_sum_le
    calc
      (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ⌊T⌋₊ + 1) : ℝ) := h_le
      _ ≤ ∑ k ∈ Finset.range (⌊T⌋₊ + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := h_split
      _ ≤ ∑ k ∈ Finset.range (⌊T⌋₊ + 1), C * Real.log T := h_bound
      _ = (⌊T⌋₊ + 1 : ℝ) * (C * Real.log T) := h_sum_simp
      _ = C * (((Finset.range (⌊T⌋₊ + 1)).image (fun k : ℕ => T + (k : ℝ))).card : ℝ) * Real.log T := by
        rw [h_card_S]
        ring

theorem deduce_extract_separated
    (model : ZetaZeroCountModel)
    (hRep : RepresentativeSelectionHypothesis model)
    (hSep : SeparatedSelectionHypothesis) :
    ExtractSeparatedHypothesis model := by
  intro σ T hT
  rcases hRep σ T hT with ⟨S, hS_interval, hS_density, C, hC_pos, h_bound⟩
  rcases hSep S 2 hS_density with ⟨W, hW_sub, hW_sep, hW_card⟩
  use W
  refine ⟨hW_sep, ?_, ?_⟩
  · intro x hx
    exact hS_interval x (hW_sub hx)
  · use C * 4
    refine ⟨by linarith, ?_⟩
    have h1 : (S.card : ℝ) ≤ 4 * (W.card : ℝ) := by
      have h_card : S.card ≤ 4 * W.card := by
        calc S.card ≤ 2 * 2 * W.card := hW_card
             _ = 4 * W.card := by ring
      exact_mod_cast h_card
    have h2 : Real.log T ≥ 0 := by
      apply Real.log_nonneg
      linarith
    calc
      (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (S.card : ℝ) * Real.log T := h_bound
      _ ≤ C * (4 * (W.card : ℝ)) * Real.log T := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · exact h1
          · exact le_of_lt hC_pos
        · exact h2
      _ = (C * 4) * (W.card : ℝ) * Real.log T := by ring

end RiemannZeta.GuthMaynard

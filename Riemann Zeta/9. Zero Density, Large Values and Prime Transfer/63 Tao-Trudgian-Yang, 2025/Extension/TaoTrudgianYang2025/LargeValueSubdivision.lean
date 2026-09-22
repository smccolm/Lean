import TaoTrudgianYang2025.LargeValuePattern

/-!
# Actual interval subdivision of a large-value pattern

Each bin is a genuine source pattern with unchanged coefficients,
support, threshold and scale, and a prescribed new physical height.
-/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

/-- The exact half-open floor bin in the source ordinate interval. -/
def LargeValuePattern.localBin (P : LargeValuePattern) (L : ℝ) (j : ℕ) : Finset ℝ := by
  classical
  exact {t ∈ P.ordinates | Nat.floor ((t-P.intervalLeft)/L) = j}

theorem LargeValuePattern.localBin_subset (P : LargeValuePattern) (L : ℝ) (j : ℕ) :
    P.localBin L j ⊆ P.ordinates := by
  classical
  exact Finset.filter_subset _ _

theorem LargeValuePattern.localBin_in_interval (P : LargeValuePattern) {L : ℝ}
    (hL : 0 < L) (j : ℕ) :
    ∀ t ∈ P.localBin L j,
      P.intervalLeft+(j : ℝ)*L ≤ t ∧ t ≤ P.intervalLeft+((j : ℝ)+1)*L := by
  classical
  intro t ht
  have hd := Finset.mem_filter.mp ht
  have ht0 := (P.ordinates_in_interval t hd.1).1
  have hn : 0 ≤ (t-P.intervalLeft)/L := div_nonneg (by linarith) hL.le
  have hlo := Nat.floor_le hn
  have hhi := Nat.lt_floor_add_one ((t-P.intervalLeft)/L)
  rw [hd.2] at hlo hhi
  have hleft := (le_div_iff₀ hL).mp hlo
  have hright := (div_lt_iff₀ hL).mp hhi
  constructor <;> linarith

/-- The local bin as a full source-pattern object, not a list of
independently asserted local estimates. -/
def LargeValuePattern.localized (P : LargeValuePattern) (L : ℝ)
    (hL : 0 < L) (j : ℕ) : LargeValuePattern :=
  { P with
    T := L
    intervalLeft := P.intervalLeft+(j : ℝ)*L
    intervalRight := P.intervalLeft+((j : ℝ)+1)*L
    ordinates := P.localBin L j
    T_pos := hL
    interval_length := by ring
    ordinates_in_interval := P.localBin_in_interval hL j
    ordinates_oneSeparated := by
      intro t ht u hu htu
      exact P.ordinates_oneSeparated t (P.localBin_subset L j ht)
        u (P.localBin_subset L j hu) htu
    large := by
      intro t ht
      exact P.large t (P.localBin_subset L j ht) }

theorem LargeValuePattern.card_eq_sum_localized (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) :
    P.ordinates.card =
      ∑ j ∈ Finset.range (Nat.floor (P.T/L)+1), (P.localized L hL j).ordinates.card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
  intro t ht
  have hp := P.ordinates_in_interval t ht
  have hdiff : t-P.intervalLeft ≤ P.T := by linarith [P.interval_length]
  have hquot := div_le_div_of_nonneg_right hdiff hL.le
  have hf := Nat.floor_mono hquot
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hf)

/-- Any proved uniform bound on the actual localized patterns sums to
the original cardinality with the literal number of bins. -/
theorem LargeValuePattern.card_le_of_localized (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (B : ℝ)
    (hbound : ∀ j ∈ Finset.range (Nat.floor (P.T/L)+1),
      ((P.localized L hL j).ordinates.card : ℝ) ≤ B) :
    (P.ordinates.card : ℝ) ≤ ((Nat.floor (P.T/L)+1 : ℕ) : ℝ)*B := by
  have hc := P.card_eq_sum_localized hL
  have hcReal : (P.ordinates.card : ℝ) =
      ∑ j ∈ Finset.range (Nat.floor (P.T/L)+1),
        ((P.localized L hL j).ordinates.card : ℝ) := by exact_mod_cast hc
  rw [hcReal]
  exact (Finset.sum_le_sum hbound).trans_eq (by simp)

end TaoTrudgianYang2025

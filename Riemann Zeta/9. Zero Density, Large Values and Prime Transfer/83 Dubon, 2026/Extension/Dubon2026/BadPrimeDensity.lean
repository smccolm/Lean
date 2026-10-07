import Dubon2026.SelectedPrimeDensity

/-! # Removing the finitely many primes dividing the fixed positive level -/

namespace Dubon2026

open Filter Set
open scoped Topology

noncomputable section

theorem selected_prime_bad_level_bound (S : ℕ → Prop) {Q : ℕ} (hQ : 0 < Q) (N : ℕ) :
    0 ≤ ((selectedPrimesUpTo S N).card : ℝ) -
      (selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ S p) N).card ∧
    ((selectedPrimesUpTo S N).card : ℝ) -
      (selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ S p) N).card ≤ Q + 1 := by
  classical
  let A := selectedPrimesUpTo S N
  let B := selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ S p) N
  have hBA : B ⊆ A := by
    intro p hp
    obtain ⟨hpN, hp, _, hS⟩ := mem_selectedPrimesUpTo.mp hp
    exact mem_selectedPrimesUpTo.mpr ⟨hpN, hp, hS⟩
  have hD : A \ B ⊆ Finset.range (Q + 1) := by
    intro p hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpN, hp, hS⟩ := mem_selectedPrimesUpTo.mp hpA
    have hd : p ∣ Q := by
      by_contra hn
      exact hpB (mem_selectedPrimesUpTo.mpr ⟨hpN, hp, hn, hS⟩)
    exact Finset.mem_range.mpr (by have := Nat.le_of_dvd hQ hd; omega)
  have hc := Finset.card_le_card hBA
  have hd := Finset.card_le_card hD
  rw [Finset.card_range, Finset.card_sdiff_of_subset hBA] at hd
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast hc)
  · exact_mod_cast hd

theorem selected_prime_density_remove_level {S : ℕ → Prop} {Q : ℕ} (hQ : 0 < Q) {d : ℝ}
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ => ((selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ S p) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 d) := by
  have hz := (tendsto_const_div_atTop_nhds_zero_nat ((Q : ℝ) + 1)).comp
    Nat.tendsto_primeCounting
  have herr : Tendsto (fun N : ℕ =>
      (((selectedPrimesUpTo S N).card : ℝ) -
        (selectedPrimesUpTo (fun p => ¬p ∣ Q ∧ S p) N).card) /
          Nat.primeCounting N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    · intro N
      exact div_nonneg (selected_prime_bad_level_bound S hQ N).1 (Nat.cast_nonneg _)
    · intro N
      exact div_le_div_of_nonneg_right (selected_prime_bad_level_bound S hQ N).2 (Nat.cast_nonneg _)
  have hh := hd.sub herr
  simp only [sub_zero] at hh
  convert hh using 1
  ext N
  ring

end

end Dubon2026

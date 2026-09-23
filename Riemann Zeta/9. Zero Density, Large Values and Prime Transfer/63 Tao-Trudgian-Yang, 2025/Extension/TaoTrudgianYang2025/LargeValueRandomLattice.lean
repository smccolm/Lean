import TaoTrudgianYang2025.LargeValuePattern

/-! The literal natural lattice in a real source interval. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

def largeValueLattice (T : ℝ) : Finset ℝ :=
  (range (Nat.floor T+1)).image (fun n : ℕ => (n:ℝ))

theorem largeValueLattice_in_interval {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ largeValueLattice T) :
    0 ≤ t ∧ t ≤ T := by
  obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
  have hn' : n ≤ Nat.floor T := Nat.le_of_lt_succ (mem_range.mp hn)
  exact ⟨Nat.cast_nonneg _,(by exact_mod_cast hn' : (n:ℝ) ≤ Nat.floor T).trans
    (Nat.floor_le hT)⟩

theorem largeValueLattice_oneSeparated (T : ℝ) : IsOneSeparated (largeValueLattice T) := by
  intro t ht u hu htu
  obtain ⟨m,_hm,rfl⟩ := mem_image.mp ht
  obtain ⟨n,_hn,rfl⟩ := mem_image.mp hu
  have hmn : m ≠ n := by intro h; subst n; exact htu rfl
  rcases lt_or_gt_of_ne hmn with h | h
  · have hs : (m:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonpos (by linarith : (m:ℝ)-(n:ℝ) ≤ 0)]
    linarith
  · have hs : (n:ℝ)+1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith : 0 ≤ (m:ℝ)-(n:ℝ))]
    linarith

theorem largeValueLattice_card (T : ℝ) :
    (largeValueLattice T).card = Nat.floor T+1 := by
  rw [largeValueLattice,card_image_of_injective _ Nat.cast_injective,card_range]

theorem largeValueLattice_card_lower (T : ℝ) :
    T ≤ ((largeValueLattice T).card:ℝ) := by
  rw [largeValueLattice_card,Nat.cast_add,Nat.cast_one]
  exact (Nat.lt_floor_add_one T).le

end TaoTrudgianYang2025


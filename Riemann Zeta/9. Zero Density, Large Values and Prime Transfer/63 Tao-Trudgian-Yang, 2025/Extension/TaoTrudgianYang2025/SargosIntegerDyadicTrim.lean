import TaoTrudgianYang2025.SargosIntegerTwoBlocks

/-! Exact bounded endpoint losses around the two rounded dyadic integer blocks. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosInteger_dyadic_omitted_card (m : ℕ) (a b : ℤ)
    (ha : (m:ℤ)-4 ≤ a) (hb : b ≤ 4*m+35) :
    (((Finset.Icc a b) \ (Finset.Ioc (m:ℤ) (4*m))).card : ℝ) ≤ 40 := by
  classical
  have hs : (Finset.Icc a b) \ (Finset.Ioc (m:ℤ) (4*m)) ⊆
      Finset.Icc ((m:ℤ)-4) m ∪ Finset.Icc ((4*m:ℤ)+1) (4*m+35) := by
    intro y hy
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc,Finset.mem_union] at hy ⊢
    omega
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hleft : (Finset.Icc ((m:ℤ)-4) m).card = 5 := by
    rw [Int.card_Icc]
    omega
  have hright : (Finset.Icc ((4*m:ℤ)+1) (4*m+35)).card = 35 := by
    rw [Int.card_Icc]
    omega
  rw [hleft,hright] at hc
  exact_mod_cast hc

theorem norm_sargosInteger_dyadic_omitted (m : ℕ) (a b : ℤ) (f : ℤ → ℂ)
    (ha : (m:ℤ)-4 ≤ a) (hb : b ≤ 4*m+35) (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖∑ y ∈ (Finset.Icc a b) \ (Finset.Ioc (m:ℤ) (4*m)), f y‖ ≤ 40 := by
  calc
    _ ≤ ∑ _y ∈ (Finset.Icc a b) \ (Finset.Ioc (m:ℤ) (4*m)), (1:ℝ) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hf y)
    _ = (((Finset.Icc a b) \ (Finset.Ioc (m:ℤ) (4*m))).card : ℝ) := by simp
    _ ≤ 40 := sargosInteger_dyadic_omitted_card m a b ha hb

theorem norm_sargosInteger_interval_le_two_dyadic (m : ℕ) (a b : ℤ) (f : ℤ → ℂ)
    (ha : (m:ℤ)-4 ≤ a) (hb : b ≤ 4*m+35) (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖∑ y ∈ Finset.Icc a b, f y‖ ≤
      2*sargosIntegerPrefixMaximum ((m:ℤ)+1) m f+
        2*sargosIntegerPrefixMaximum ((2*m:ℤ)+1) (2*m) f+40 := by
  classical
  rw [← Finset.sum_inter_add_sum_diff (Finset.Icc a b) (Finset.Ioc (m:ℤ) (4*m)) f]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_sargosInteger_intersection_two_dyadic m a b f)
      (norm_sargosInteger_dyadic_omitted m a b f ha hb hf))

end TaoTrudgianYang2025


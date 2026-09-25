import TaoTrudgianYang2025.AdditiveEnergy

/-! Finite integer interval counts with exact endpoint loss. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_card_le_interval_length_add_one (S : Finset ℤ) {a b : ℝ}
    (hab : a ≤ b) (hmem : ∀ n ∈ S, a ≤ (n:ℝ) ∧ (n:ℝ) ≤ b) :
    (S.card:ℝ) ≤ b-a+1 := by
  classical
  let W := S.image (fun n : ℤ => (n:ℝ))
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hy
    have hmn : m-n ≠ 0 := by
      intro he
      apply hxy
      exact congrArg (fun z : ℤ => (z:ℝ)) (sub_eq_zero.mp he)
    have hpos : 0 < |m-n| := abs_pos.mpr hmn
    have hbound : (1:ℤ) ≤ |m-n| := by omega
    exact_mod_cast hbound
  have hW : ∀ x ∈ W, a ≤ x ∧ x ≤ b := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    exact hmem n hn
  have hb := oneSeparated_card_cast_le_interval_length_add_one W hsep
    (sub_nonneg.mpr hab) hW
  have hcard : W.card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => Int.cast_injective h)
  rwa [hcard] at hb

theorem integer_card_le_of_abs_sub_le (S : Finset ℤ) {a B : ℝ}
    (hB : 0 ≤ B) (hmem : ∀ n ∈ S, |(n:ℝ)-a| ≤ B) :
    (S.card:ℝ) ≤ 2*B+1 := by
  have hb := integer_card_le_interval_length_add_one S (by linarith : a-B ≤ a+B)
    (fun n hn => by
      rcases abs_le.mp (hmem n hn) with ⟨hl,hu⟩
      constructor <;> linarith)
  linarith

end TaoTrudgianYang2025


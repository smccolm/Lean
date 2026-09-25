import TaoTrudgianYang2025.IntegerBoxCount

/-! Four-coordinate closed-box counts, represented as an integer triple and one integer. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_box_quadruples_card_le
    (S : Finset ((ℤ × ℤ × ℤ) × ℤ)) {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    (hx : ∀ p ∈ S, (p.1.1:ℝ) ∈ Set.Icc a₁ b₁)
    (hy : ∀ p ∈ S, (p.1.2.1:ℝ) ∈ Set.Icc a₂ b₂)
    (hz : ∀ p ∈ S, (p.1.2.2:ℝ) ∈ Set.Icc a₃ b₃)
    (hw : ∀ p ∈ S, (p.2:ℝ) ∈ Set.Icc a₄ b₄) :
    (S.card:ℝ) ≤ (b₁-a₁+1)*(b₂-a₂+1)*(b₃-a₃+1)*(b₄-a₄+1) := by
  classical
  let X := S.image Prod.fst
  let Y := S.image Prod.snd
  have hX : (X.card:ℝ) ≤ (b₁-a₁+1)*(b₂-a₂+1)*(b₃-a₃+1) :=
    integer_box_triples_card_le X h₁ h₂ h₃
      (fun x hx' => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx'
        exact hx p hp)
      (fun y hy' => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy'
        exact hy p hp)
      (fun z hz' => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz'
        exact hz p hp)
  have hY : (Y.card:ℝ) ≤ b₄-a₄+1 :=
    integer_card_le_interval_length_add_one Y h₄ (fun y hy' => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy'
      exact hw p hp)
  have hsub : S ⊆ X ×ˢ Y := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  have hc : S.card ≤ X.card*Y.card := by
    simpa only [Finset.card_product] using Finset.card_le_card hsub
  have hcR : (S.card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by exact_mod_cast hc
  exact hcR.trans (mul_le_mul hX hY (by positivity)
    (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)))

end TaoTrudgianYang2025


import TaoTrudgianYang2025.IntegerIntervalCount

/-! Actual integer triples in closed real boxes, with endpoint losses. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_box_triples_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (hx : ∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc a₁ b₁)
    (hy : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc a₂ b₂)
    (hz : ∀ p ∈ S, (p.2.2:ℝ) ∈ Set.Icc a₃ b₃) :
    (S.card:ℝ) ≤ (b₁-a₁+1)*(b₂-a₂+1)*(b₃-a₃+1) := by
  classical
  let X := S.image (fun p => p.1)
  let Y := S.image (fun p => p.2.1)
  let Z := S.image (fun p => p.2.2)
  have hX : (X.card:ℝ) ≤ b₁-a₁+1 :=
    integer_card_le_interval_length_add_one X h₁ (fun x hx' => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx'
      exact hx p hp)
  have hY : (Y.card:ℝ) ≤ b₂-a₂+1 :=
    integer_card_le_interval_length_add_one Y h₂ (fun y hy' => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy'
      exact hy p hp)
  have hZ : (Z.card:ℝ) ≤ b₃-a₃+1 :=
    integer_card_le_interval_length_add_one Z h₃ (fun z hz' => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz'
      exact hz p hp)
  have hsub : S ⊆ X ×ˢ (Y ×ˢ Z) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩
  have hc : S.card ≤ X.card*(Y.card*Z.card) := by
    simpa only [Finset.card_product] using Finset.card_le_card hsub
  have hcR : (S.card:ℝ) ≤ (X.card:ℝ)*((Y.card:ℝ)*(Z.card:ℝ)) := by exact_mod_cast hc
  calc
    _ ≤ (X.card:ℝ)*((Y.card:ℝ)*(Z.card:ℝ)) := hcR
    _ ≤ (b₁-a₁+1)*((b₂-a₂+1)*(b₃-a₃+1)) :=
      mul_le_mul hX (mul_le_mul hY hZ (by positivity) (by linarith))
        (by positivity) (by linarith)
    _ = _ := by ring

end TaoTrudgianYang2025


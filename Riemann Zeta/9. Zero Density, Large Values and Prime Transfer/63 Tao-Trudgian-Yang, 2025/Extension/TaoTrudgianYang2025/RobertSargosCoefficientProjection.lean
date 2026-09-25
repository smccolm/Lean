import TaoTrudgianYang2025.IntegerBoxCount
import TaoTrudgianYang2025.RobertSargosPrimitiveProjection

/-! The actual coefficient projection of the primitive source system. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_coefficient_image_card_le_box
    (S : Finset RobertSargosPoint) {R H Q δ : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) :
    ((S.image robertSargosCoefficientKey).card:ℝ) ≤ (2*R+1)*(H+1)^2 := by
  have hb := integer_box_triples_card_le (S.image robertSargosCoefficientKey)
    (by linarith : -R ≤ R) (by linarith : H ≤ 2*H) (by linarith : H ≤ 2*H)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact abs_le.mp (hmem p hp).r_bound)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).h₁_support)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).h₂_support)
  calc
    _ ≤ (R-(-R)+1)*(2*H-H+1)*(2*H-H+1) := hb
    _ = _ := by ring

theorem robertSargos_coefficient_image_card_le
    (S : Finset RobertSargosPoint) {R H Q δ : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) :
    ((S.image robertSargosCoefficientKey).card:ℝ) ≤ 12*R*H^2 := by
  have hb := robertSargos_coefficient_image_card_le_box S (by linarith) (by linarith) hmem
  have hsq : (H+1)^2 ≤ (2*H)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc
    _ ≤ (2*R+1)*(H+1)^2 := hb
    _ ≤ (3*R)*(2*H)^2 := mul_le_mul (by linarith) hsq (sq_nonneg _) (by linarith)
    _ = _ := by ring

end TaoTrudgianYang2025


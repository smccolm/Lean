import TaoTrudgianYang2025.RobertSargosPrimitiveSystem
import TaoTrudgianYang2025.IntegerQuadrupleCount

/-! Projection for the direct product/divisor count in the large-tolerance regime. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosProductKey (p : RobertSargosPoint) : (ℤ × ℤ × ℤ) × ℤ :=
  ((p.r,p.h₁,p.q₁),p.d)

theorem robertSargos_product_key_injective {p q : RobertSargosPoint}
    (hk : robertSargosProductKey p = robertSargosProductKey q)
    (hh : p.h₂ = q.h₂) (hq : p.q₂ = q.q₂) : p = q := by
  cases p
  cases q
  simp_all [robertSargosProductKey]

theorem robertSargos_product_image_card_le_box
    (S : Finset RobertSargosPoint) {R H Q δ : ℝ}
    (hR : 0 ≤ R) (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) :
    ((S.image robertSargosProductKey).card:ℝ) ≤
      (2*R+1)*(H+1)*(4*Q+1)*(2*(δ+8)*Q+1) := by
  have hb := integer_box_quadruples_card_le (S.image robertSargosProductKey)
    (a₁ := -R) (b₁ := R) (a₂ := H) (b₂ := 2*H)
    (a₃ := -(2*Q)) (b₃ := 2*Q) (a₄ := -((δ+8)*Q)) (b₄ := (δ+8)*Q)
    (by linarith) (by linarith) (by linarith)
    (by have hD : 0 ≤ (δ+8)*Q := by positivity
        linarith)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact abs_le.mp (hmem p hp).r_bound)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).h₁_support)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact abs_le.mp (hmem p hp).q₁_support.2)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact abs_le.mp ((hmem p hp).displacement_le hH hQ))
  convert hb using 1
  ring

theorem robertSargos_product_image_card_le
    (S : Finset RobertSargosPoint) {R H Q δ : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q) (hδ : 1 ≤ δ)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) :
    ((S.image robertSargosProductKey).card:ℝ) ≤ 570*δ*R*H*Q^2 := by
  have hR0 : 0 ≤ R := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hδQ : 1 ≤ δ*Q := one_le_mul_of_one_le_of_one_le hδ hQ
  have hlast : 2*(δ+8)*Q+1 ≤ 19*δ*Q := by
    have hm := mul_le_mul_of_nonneg_right hδ hQ0
    nlinarith only [hm,hδQ]
  have hb := robertSargos_product_image_card_le_box S hR0 (by linarith)
    (by linarith) hδ0 hmem
  calc
    _ ≤ (2*R+1)*(H+1)*(4*Q+1)*(2*(δ+8)*Q+1) := hb
    _ ≤ (3*R)*(2*H)*(5*Q)*(19*δ*Q) :=
      mul_le_mul
        (mul_le_mul
          (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
          (by linarith) (by positivity) (by positivity))
        hlast (by positivity) (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025

import TaoTrudgianYang2025.RobertSargosSevenSystem
import TaoTrudgianYang2025.IntegerQuadrupleCount

/-! Four-coordinate source keys for the zero-displacement factor-pair count. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosZeroKey (p : RobertSargosSevenPoint) : (ℤ × ℤ × ℤ) × ℤ :=
  ((p.r,p.h₁,p.q₁),p.n₂)

theorem robertSargos_zero_key_injective {p q : RobertSargosSevenPoint}
    (hk : robertSargosZeroKey p = robertSargosZeroKey q)
    (hh : p.h₂ = q.h₂) (hq : p.q₂ = q.q₂)
    (hp0 : p.n₁ = p.n₂) (hq0 : q.n₁ = q.n₂) : p = q := by
  cases p
  cases q
  simp_all [robertSargosZeroKey]

theorem RobertSargosSevenSystem.zero_product {R H Q N δ : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosSevenSystem R H Q N δ p)
    (hzero : p.n₁ = p.n₂) : p.h₂*p.q₂ = p.h₁*p.q₁ := by
  have hl := h.linear
  rw [hzero] at hl
  linarith

theorem robertSargos_zero_image_card_le
    (S : Finset RobertSargosSevenPoint) {R H Q N δ : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (hmem : ∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) :
    ((S.image robertSargosZeroKey).card:ℝ) ≤ 30*R*H*Q*N := by
  have hR0 : 0 ≤ R := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hb := integer_box_quadruples_card_le (S.image robertSargosZeroKey)
    (a₁ := -R) (b₁ := R) (a₂ := H) (b₂ := 2*H)
    (a₃ := -(2*Q)) (b₃ := 2*Q) (a₄ := 1) (b₄ := N)
    (by linarith) (by linarith) (by linarith) hN
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
      exact (hmem p hp).n₂_support)
  have hb' : ((S.image robertSargosZeroKey).card:ℝ) ≤
      (2*R+1)*(H+1)*(4*Q+1)*N := by
    convert hb using 1
    ring
  calc
    _ ≤ (2*R+1)*(H+1)*(4*Q+1)*N := hb'
    _ ≤ ((3*R)*(2*H)*(5*Q))*N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul
          (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
          (by linarith) (by positivity) (by positivity)) hN0
    _ = _ := by ring

end TaoTrudgianYang2025


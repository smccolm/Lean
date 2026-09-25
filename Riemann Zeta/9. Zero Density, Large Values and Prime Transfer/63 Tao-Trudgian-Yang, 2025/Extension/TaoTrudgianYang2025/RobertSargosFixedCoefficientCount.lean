import TaoTrudgianYang2025.PrimitiveTripleCount
import TaoTrudgianYang2025.RobertSargosRatioGeometry

/-! An actual consumer of the conic-strip geometry and primitive-triple count.
This is the positive-r, positive-q fixed-coefficient branch of Section 3.3(b);
the total six- and seven-variable counts are separate remaining obligations. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_primitive_positive_fixed_coeff_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {r : ℕ} {h₁ h₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd (-h₂) h₁ : ℤ) r = 1)
    (hr : 0 < r) (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hrH : (r:ℝ) ≤ H/2) (hh₁ : H ≤ (h₁:ℝ)) (hh₂ : H ≤ (h₂:ℝ))
    (hq₁ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc Q (2*Q))
    (hq₂ : ∀ p ∈ S, Q ≤ (p.1:ℝ))
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, (r:ℤ)*p.2.2+h₁*p.2.1-h₂*p.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced r p.2.1 p.1 h₁ h₂ p.2.2| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (r.divisors.card:ℝ)+
      32*δ*Q^2/(H*(r:ℝ))*(∑ g ∈ r.divisors, (g:ℝ)) := by
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  let A := Real.sqrt ((h₁:ℝ)*(h₁-r)/((h₂:ℝ)*(h₂-r)))
  let e := 4*δ*(r:ℝ)/H
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hratio : ∀ p ∈ S,
      A-e ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+e := by
    intro p hp
    have hp₁ : 0 < (p.2.1:ℝ) := hQ.trans_le (hq₁ p hp).1
    have hp₂ : 0 < (p.1:ℝ) := hQ.trans_le (hq₂ p hp)
    have hl : (r:ℝ)*p.2.2+(h₁:ℝ)*p.2.1-(h₂:ℝ)*p.1 = 0 := by
      exact_mod_cast hline p hp
    have hb := robertSargos_ratio_sqrt_gap hH hQ hδ
      (by simpa only [abs_of_pos hrp] using hrH) hh₁ hh₂
      (by simpa only [abs_of_pos hp₁] using hq₁ p hp)
      (by simpa only [abs_of_pos hp₂] using hq₂ p hp)
      (mul_pos hp₁ hp₂) hl (hnear p hp)
    rw [abs_of_pos hrp] at hb
    change |(p.1:ℝ)/p.2.1-A| ≤ e at hb
    rcases abs_le.mp hb with ⟨hlow,hupp⟩
    constructor <;> linarith
  have hb := primitive_linear_triple_card_le S hcoeff hr hQ (by linarith : A-e ≤ A+e)
    (fun p hp => hq₁ p hp) hprim
    (fun p hp => by have hl := hline p hp; nlinarith only [hl]) hratio
  calc
    (S.card:ℝ) ≤ (r.divisors.card:ℝ)+
        4*Q^2*((A+e)-(A-e))/(r:ℝ)^2*(∑ g ∈ r.divisors, (g:ℝ)) := hb
    _ = _ := by dsimp [e]; field_simp; ring

end TaoTrudgianYang2025


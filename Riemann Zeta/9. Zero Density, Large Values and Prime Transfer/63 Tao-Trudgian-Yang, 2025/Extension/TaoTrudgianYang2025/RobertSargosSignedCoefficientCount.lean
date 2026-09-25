import TaoTrudgianYang2025.PrimitiveTripleSignedCount
import TaoTrudgianYang2025.RobertSargosRatioGeometry

/-! The positive-q conic count with either sign of the nonzero coefficient r. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_primitive_positive_q_fixed_coeff_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {r h₁ h₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd (-h₂) h₁ : ℤ) r = 1)
    (hr : r ≠ 0) (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hrH : |(r:ℝ)| ≤ H/2) (hh₁ : H ≤ (h₁:ℝ)) (hh₂ : H ≤ (h₂:ℝ))
    (hq₁ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc Q (2*Q))
    (hq₂ : ∀ p ∈ S, Q ≤ (p.1:ℝ))
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, (r:ℤ)*p.2.2+h₁*p.2.1-h₂*p.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced r p.2.1 p.1 h₁ h₂ p.2.2| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (r.natAbs.divisors.card:ℝ)+
      32*δ*Q^2/(H*|(r:ℝ)|)*(∑ g ∈ r.natAbs.divisors, (g:ℝ)) := by
  have hrn : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have hrp : 0 < |(r:ℝ)| := abs_pos.mpr hrn
  have hrc : (r.natAbs:ℝ) = |(r:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs r)
  let A := Real.sqrt ((h₁:ℝ)*(h₁-r)/((h₂:ℝ)*(h₂-r)))
  let e := 4*δ*|(r:ℝ)|/H
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hratio : ∀ p ∈ S,
      A-e ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+e := by
    intro p hp
    have hp₁ : 0 < (p.2.1:ℝ) := hQ.trans_le (hq₁ p hp).1
    have hp₂ : 0 < (p.1:ℝ) := hQ.trans_le (hq₂ p hp)
    have hl : (r:ℝ)*p.2.2+(h₁:ℝ)*p.2.1-(h₂:ℝ)*p.1 = 0 := by
      exact_mod_cast hline p hp
    have hb := robertSargos_ratio_sqrt_gap hH hQ hδ
      hrH hh₁ hh₂
      (by simpa only [abs_of_pos hp₁] using hq₁ p hp)
      (by simpa only [abs_of_pos hp₂] using hq₂ p hp)
      (mul_pos hp₁ hp₂) hl (hnear p hp)
    change |(p.1:ℝ)/p.2.1-A| ≤ e at hb
    rcases abs_le.mp hb with ⟨hlow,hupp⟩
    constructor <;> linarith
  have hb := primitive_linear_triple_card_le_abs_modulus S hcoeff hr hQ (by linarith : A-e ≤ A+e)
    (fun p hp => hq₁ p hp) hprim
    (fun p hp => by have hl := hline p hp; nlinarith only [hl]) hratio
  calc
    (S.card:ℝ) ≤ (r.natAbs.divisors.card:ℝ)+
        4*Q^2*((A+e)-(A-e))/(r.natAbs:ℝ)^2*(∑ g ∈ r.natAbs.divisors, (g:ℝ)) := hb
    _ = _ := by rw [hrc]; dsimp [e]; field_simp; ring

end TaoTrudgianYang2025

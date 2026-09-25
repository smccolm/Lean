import TaoTrudgianYang2025.PrimitiveTripleCount

/-! The arithmetic count is insensitive to the sign of the nonzero modulus. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem primitive_linear_triple_card_le_abs_modulus
    (S : Finset (ℤ × ℤ × ℤ)) {a b c : ℤ} {V α β : ℝ}
    (hcoeff : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : c ≠ 0)
    (hV : 0 < V) (hαβ : α ≤ β)
    (hden : ∀ p ∈ S, V ≤ (p.2.1:ℝ) ∧ (p.2.1:ℝ) ≤ 2*V)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, a*p.1+b*p.2.1+c*p.2.2 = 0)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ β) :
    (S.card:ℝ) ≤ (c.natAbs.divisors.card:ℝ)+
      4*V^2*(β-α)/(c.natAbs:ℝ)^2*(∑ g ∈ c.natAbs.divisors, (g:ℝ)) := by
  have hcN : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hcn : (c.natAbs:ℤ) = -c := by rw [Int.natCast_natAbs,abs_of_neg hneg]
    have hp : Int.gcd (Int.gcd (-a) (-b) : ℤ) c.natAbs = 1 := by
      simpa only [hcn,Int.neg_gcd,Int.gcd_neg] using hcoeff
    apply primitive_linear_triple_card_le S hp hcN hV hαβ hden hprim _ hratio
    intro p hp
    rw [hcn]
    have hl := hline p hp
    nlinarith only [hl]
  · have hcn : (c.natAbs:ℤ) = c := by rw [Int.natCast_natAbs,abs_of_pos hpos]
    have hp : Int.gcd (Int.gcd a b : ℤ) c.natAbs = 1 := by rwa [hcn]
    apply primitive_linear_triple_card_le S hp hcN hV hαβ hden hprim _ hratio
    intro p hp
    simpa only [hcn] using hline p hp

end TaoTrudgianYang2025

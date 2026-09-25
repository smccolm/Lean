import TaoTrudgianYang2025.RobertSargosFixedDisplacementSafe

/-! The complementary fixed-displacement bound from the actual linear-ratio strip. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_fixed_displacement_linear_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d q₁ q₂ : ℤ} {R H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1) (hd : d ≠ 0)
    (hR : 0 ≤ R) (hH : 0 < H) (hQ : 0 < Q) (hδ : δ ≤ 1)
    (hq₁ : |(q₁:ℝ)| ∈ Set.Icc Q (2*Q)) (hq₂ : |(q₂:ℝ)| ∈ Set.Icc Q (2*Q))
    (hsign : 0 < q₁*q₂)
    (hh₁ : ∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc H (2*H))
    (hh₂ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H))
    (hr : ∀ p ∈ S, |(p.2.2:ℝ)| ≤ R)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1)
    (hline : ∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (d.natAbs.divisors.card:ℝ)+
      72*H*R/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := by
  have hc : Int.gcd (Int.gcd q₁ (-q₂) : ℤ) d = 1 := by
    rw [Int.gcd_neg,Int.gcd_assoc,Int.gcd_comm q₂ d,← Int.gcd_assoc,Int.gcd_comm q₁ d]
    exact hcoeff
  have hp : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1 := by
    intro p hp
    rw [Int.gcd_assoc,Int.gcd_comm p.2.1 p.2.2,← Int.gcd_assoc,Int.gcd_comm p.1 p.2.2]
    exact hprim p hp
  let A := (q₂:ℝ)/q₁
  let e := 9*R/H
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsignR : 0 < (q₁:ℝ)*q₂ := by exact_mod_cast hsign
  have hratio : ∀ p ∈ S, A-e ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+e := by
    intro p hp
    have hl : (p.2.2:ℝ)*d+(p.1:ℝ)*q₁-(p.2.1:ℝ)*q₂ = 0 := by
      have hli := hline p hp
      have hh : p.2.2*d+p.1*q₁-p.2.1*q₂ = 0 := by nlinarith only [hli]
      exact_mod_cast hh
    have hb := robertSargos_coefficient_linear_source_gap hH hQ hδ (hr p hp)
      (hh₁ p hp) (hh₂ p hp) hq₁ hq₂ hsignR hl (hnear p hp)
    change |(p.1:ℝ)/p.2.1-A| ≤ e at hb
    rcases abs_le.mp hb with ⟨hlow,hupp⟩
    constructor <;> linarith
  have hb := primitive_linear_triple_card_le_abs_modulus S hc hd hH
    (by linarith : A-e ≤ A+e) (fun p hp => hh₂ p hp) hp
    (fun p hp => by have hl := hline p hp; nlinarith only [hl]) hratio
  calc
    _ ≤ (d.natAbs.divisors.card:ℝ)+
      4*H^2*((A+e)-(A-e))/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := hb
    _ = _ := by dsimp [e]; field_simp; ring

end TaoTrudgianYang2025


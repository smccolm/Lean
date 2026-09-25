import TaoTrudgianYang2025.PrimitiveTripleSignedCount
import TaoTrudgianYang2025.RobertSargosConicOrientation

/-! Counting actual coefficient triples with a fixed safe conic pivot. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_fixed_displacement_safe_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d q₁ q₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1) (hd : d ≠ 0)
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hq₁ : Q ≤ |(q₁:ℝ)|) (hsafe : 0 ≤ (q₁:ℝ)*d)
    (hh₂ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H))
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1)
    (hline : ∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (d.natAbs.divisors.card:ℝ)+
      8*H^2*δ/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := by
  have hc : Int.gcd (Int.gcd q₁ (-q₂) : ℤ) d = 1 := by
    rw [Int.gcd_neg,Int.gcd_assoc,Int.gcd_comm q₂ d,← Int.gcd_assoc,Int.gcd_comm q₁ d]
    exact hcoeff
  have hp : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1 := by
    intro p hp
    rw [Int.gcd_assoc,Int.gcd_comm p.2.1 p.2.2,← Int.gcd_assoc,Int.gcd_comm p.1 p.2.2]
    exact hprim p hp
  let A := (q₂:ℝ)*(q₂-d)/((q₁:ℝ)*(q₁+d))
  have hratio : ∀ p ∈ S, A-δ ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+δ := by
    intro p hp
    have hl : (p.2.2:ℝ)*d+(p.1:ℝ)*q₁-(p.2.1:ℝ)*q₂ = 0 := by
      have hli := hline p hp
      have hh : p.2.2*d+p.1*q₁-p.2.1*q₂ = 0 := by nlinarith only [hli]
      exact_mod_cast hh
    have hb := robertSargos_coefficient_conic_ratio_gap hH hQ hδ
      (hh₂ p hp).1 hq₁ hsafe hl (hnear p hp)
    change |(p.1:ℝ)/p.2.1-A| ≤ δ at hb
    rcases abs_le.mp hb with ⟨hlow,hupp⟩
    constructor <;> linarith
  have hb := primitive_linear_triple_card_le_abs_modulus S hc hd hH
    (by linarith : A-δ ≤ A+δ) (fun p hp => hh₂ p hp) hp
    (fun p hp => by have hl := hline p hp; nlinarith only [hl]) hratio
  calc
    _ ≤ (d.natAbs.divisors.card:ℝ)+
      4*H^2*((A+δ)-(A-δ))/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := hb
    _ = _ := by ring

end TaoTrudgianYang2025


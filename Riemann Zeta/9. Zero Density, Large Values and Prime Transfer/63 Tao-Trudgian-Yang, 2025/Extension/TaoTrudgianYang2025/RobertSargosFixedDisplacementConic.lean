import TaoTrudgianYang2025.RobertSargosFixedDisplacementSafe

/-! The full fixed-displacement conic count, using either safe pivot. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_fixed_displacement_conic_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d q₁ q₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1) (hd : d ≠ 0)
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hq₁ : Q ≤ |(q₁:ℝ)|) (hq₂ : Q ≤ |(q₂:ℝ)|) (hsign : 0 < q₁*q₂)
    (hh₁ : ∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc H (2*H))
    (hh₂ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H))
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1)
    (hline : ∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (d.natAbs.divisors.card:ℝ)+
      8*H^2*δ/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := by
  classical
  have hsignR : 0 < (q₁:ℝ)*q₂ := by exact_mod_cast hsign
  rcases robertSargos_safe_pivot (d := (d:ℝ)) hsignR with hs | hs
  · exact robertSargos_fixed_displacement_safe_card_le S hcoeff hd hH hQ hδ hq₁ hs
      hh₂ hprim hline hnear
  · let f : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun p => (p.2.1,p.1,p.2.2)
    let W := S.image f
    have hc : Int.gcd (Int.gcd (-d) q₂ : ℤ) q₁ = 1 := by
      rw [Int.neg_gcd,Int.gcd_assoc,Int.gcd_comm q₂ q₁,← Int.gcd_assoc]
      exact hcoeff
    have hden : ∀ p ∈ W, (p.2.1:ℝ) ∈ Set.Icc H (2*H) := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact hh₁ q hq
    have hWp : ∀ p ∈ W, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      dsimp [f]
      rw [Int.gcd_assoc,Int.gcd_comm q.2.1 q.1,← Int.gcd_assoc]
      exact hprim q hq
    have hWl : ∀ p ∈ W, p.2.2*(-d)+q₂*p.1-q₁*p.2.1 = 0 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      dsimp [f]
      have hl := hline q hq
      nlinarith only [hl]
    have hWn : ∀ p ∈ W,
        |robertSargosReduced p.2.2 q₂ q₁ p.1 p.2.1 (-d)| ≤ δ*H*Q^2 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hl : (q.2.2:ℝ)*d+(q.1:ℝ)*q₁-(q.2.1:ℝ)*q₂ = 0 := by
        have hli := hline q hq
        have hz : q.2.2*d+q.1*q₁-q.2.1*q₂ = 0 := by nlinarith only [hli]
        exact_mod_cast hz
      simpa only [f,Int.cast_neg,robertSargosReduced_swap hl,abs_neg] using hnear q hq
    have hb := robertSargos_fixed_displacement_safe_card_le W hc (neg_ne_zero.mpr hd)
      hH hQ hδ hq₂ (by simpa only [Int.cast_neg] using hs) hden hWp hWl
      (by simpa only [Int.cast_neg] using hWn)
    have hinj : Function.Injective f := by
      intro p q he
      have he' := congrArg f he
      simpa only [f,Prod.mk.eta] using he'
    have hcard : W.card = S.card := Finset.card_image_of_injective S hinj
    simpa only [hcard,Int.natAbs_neg] using hb

end TaoTrudgianYang2025

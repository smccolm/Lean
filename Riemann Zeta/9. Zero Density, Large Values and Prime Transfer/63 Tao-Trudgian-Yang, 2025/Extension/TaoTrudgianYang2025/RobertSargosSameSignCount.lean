import TaoTrudgianYang2025.RobertSargosSignedCoefficientCount

/-! The full same-sign-q fixed-coefficient branch of Robert--Sargos (2002),
Section 3.3(b), with the source's gcd order and both signs retained. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_primitive_fixed_coeff_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {r h₁ h₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd r h₁ : ℤ) h₂ = 1)
    (hr : r ≠ 0) (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hrH : |(r:ℝ)| ≤ H/2) (hh₁ : H ≤ (h₁:ℝ)) (hh₂ : H ≤ (h₂:ℝ))
    (hq₁ : ∀ p ∈ S, |(p.2.1:ℝ)| ∈ Set.Icc Q (2*Q))
    (hq₂ : ∀ p ∈ S, Q ≤ |(p.1:ℝ)|)
    (hsign : ∀ p ∈ S, 0 < p.2.1*p.1)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.2.1 : ℤ) p.1 = 1)
    (hline : ∀ p ∈ S, r*p.2.2+h₁*p.2.1-h₂*p.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced r p.2.1 p.1 h₁ h₂ p.2.2| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ 2*(r.natAbs.divisors.card:ℝ)+
      64*δ*Q^2/(H*|(r:ℝ)|)*(∑ g ∈ r.natAbs.divisors, (g:ℝ)) := by
  classical
  have hc : Int.gcd (Int.gcd (-h₂) h₁ : ℤ) r = 1 := by
    rw [Int.neg_gcd,Int.gcd_comm h₂ h₁,Int.gcd_assoc,Int.gcd_comm h₂ r,
      ← Int.gcd_assoc,Int.gcd_comm h₁ r]
    exact hcoeff
  have hpp : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1 := by
    intro p hp
    rw [Int.gcd_comm p.1 p.2.1,Int.gcd_assoc,Int.gcd_comm p.1 p.2.2,
      ← Int.gcd_assoc,Int.gcd_comm p.2.1 p.2.2]
    exact hprim p hp
  let P := S.filter (fun p => 0 < p.2.1)
  let N := S.filter (fun p => ¬ 0 < p.2.1)
  let f : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun p => (-p.1,-p.2.1,-p.2.2)
  let M := N.image f
  have hpos : ∀ p ∈ P, 0 < (p.2.1:ℝ) ∧ 0 < (p.1:ℝ) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hu : 0 < p.1 := (mul_pos_iff.mp (hsign p hp'.1)).resolve_right
      (by intro hn; omega) |>.2
    exact ⟨by exact_mod_cast hp'.2,by exact_mod_cast hu⟩
  have hneg : ∀ p ∈ N, (p.2.1:ℝ) < 0 ∧ (p.1:ℝ) < 0 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hn := (mul_pos_iff.mp (hsign p hp'.1)).resolve_left (by intro hh; omega)
    exact ⟨by exact_mod_cast hn.1,by exact_mod_cast hn.2⟩
  have hbP := robertSargos_primitive_positive_q_fixed_coeff_card_le P hc hr hH hQ hδ
    hrH hh₁ hh₂
    (fun p hp => by
      simpa only [abs_of_pos (hpos p hp).1] using hq₁ p (Finset.mem_filter.mp hp).1)
    (fun p hp => by
      simpa only [abs_of_pos (hpos p hp).2] using hq₂ p (Finset.mem_filter.mp hp).1)
    (fun p hp => hpp p (Finset.mem_filter.mp hp).1)
    (fun p hp => hline p (Finset.mem_filter.mp hp).1)
    (fun p hp => hnear p (Finset.mem_filter.mp hp).1)
  have hMden : ∀ p ∈ M, (p.2.1:ℝ) ∈ Set.Icc Q (2*Q) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa only [f,Int.cast_neg,abs_of_neg (hneg q hq).1] using
      hq₁ q (Finset.mem_filter.mp hq).1
  have hMnum : ∀ p ∈ M, Q ≤ (p.1:ℝ) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa only [f,Int.cast_neg,abs_of_neg (hneg q hq).2] using
      hq₂ q (Finset.mem_filter.mp hq).1
  have hMprim : ∀ p ∈ M, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa only [f,Int.neg_gcd,Int.gcd_neg] using hpp q (Finset.mem_filter.mp hq).1
  have hMline : ∀ p ∈ M, r*p.2.2+h₁*p.2.1-h₂*p.1 = 0 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hl := hline q (Finset.mem_filter.mp hq).1
    dsimp [f]
    nlinarith only [hl]
  have hMnear : ∀ p ∈ M,
      |robertSargosReduced r p.2.1 p.1 h₁ h₂ p.2.2| ≤ δ*H*Q^2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa only [f,Int.cast_neg,robertSargosReduced_neg] using
      hnear q (Finset.mem_filter.mp hq).1
  have hbM := robertSargos_primitive_positive_q_fixed_coeff_card_le M hc hr hH hQ hδ
    hrH hh₁ hh₂ hMden hMnum hMprim hMline hMnear
  have hinj : Function.Injective f := by
    intro p q he
    have he' := congrArg f he
    simpa only [f,neg_neg,Prod.mk.eta] using he'
  have hcardM : M.card = N.card := Finset.card_image_of_injective N hinj
  have hcard : P.card+N.card = S.card := Finset.card_filter_add_card_filter_not _
  have hcardR : (P.card:ℝ)+(N.card:ℝ) = (S.card:ℝ) := by exact_mod_cast hcard
  rw [hcardM] at hbM
  calc
    (S.card:ℝ) = (P.card:ℝ)+(N.card:ℝ) := hcardR.symm
    _ ≤ _ := add_le_add hbP hbM
    _ = _ := by ring

end TaoTrudgianYang2025

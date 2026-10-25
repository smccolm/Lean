import Dubon2026.SourceOrderTwelveBasic

/-! DUB-17/18 -> characteristic-two genus/Picard -> weighted exceptional
census -> exact orbit sizes and involution/cubic fixed-point marks for the
actual order-twelve sign quotient. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve.
Only the source dependency chain to these exact marks is retained. The
actual elliptic quotient must discharge the order/exponent hypotheses. -/
namespace Dubon2026.SourceOrderTwelve
open MulAction Subgroup
noncomputable section
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
include hG hexp

theorem sylow_three_not_normal (P : Sylow 3 G) : ¬(P : Subgroup G).Normal := by
  intro hn
  have hP := card_sylow_three hG P

  haveI : Finite (P : Subgroup G) := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨⟨c, hcP⟩, hc1⟩ : ∃ c : (P : Subgroup G), c ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card (P : Subgroup G) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => by rw [h a, h b]⟩
    omega
  have hc1 : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hoc : orderOf c = 3 := orderOf_eq_three_of_mem hP hcP hc1

  have hconj : ∀ x : G, x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c ^ 2 := by
    intro x
    have hm : x * c * x⁻¹ ∈ (P : Subgroup G) := hn.conj_mem c hcP x
    rcases mem_of_card_three hP hcP hc1 hm with h | h | h
    · exfalso; apply hc1
      have : c = x⁻¹ * (x * c * x⁻¹) * x := by group
      rw [this, h]; group
    · exact Or.inl h
    · exact Or.inr h

  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hQ := card_sylow_two hG Q
  haveI : Finite (Q : Subgroup G) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have hQexp : ∀ q : G, q ∈ (Q : Subgroup G) → q ^ 2 = 1 := by
    intro q hq
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro h3
    have : orderOf q ∣ 4 := hQ ▸ Subgroup.orderOf_dvd_natCard (Q : Subgroup G) hq
    rw [h3] at this; norm_num at this
  obtain ⟨q₁, hq₁Q, hq₁⟩ : ∃ q₁ : G, q₁ ∈ (Q : Subgroup G) ∧ q₁ ≠ 1 := by
    by_contra h; push Not at h
    have : Nat.card (Q : Subgroup G) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext (by rw [h a a.2, h b b.2])⟩
    omega
  obtain ⟨q₂, hq₂Q, hq₂, hq₂₁⟩ : ∃ q₂ : G, q₂ ∈ (Q : Subgroup G) ∧ q₂ ≠ 1 ∧ q₂ ≠ q₁ := by
    by_contra h; push Not at h
    have : Nat.card (Q : Subgroup G) ≤ 2 := by
      let f : Bool → (Q : Subgroup G) := fun b => if b then ⟨q₁, hq₁Q⟩ else 1
      have hf : Function.Surjective f := by
        rintro ⟨q, hq⟩
        by_cases hq1 : q = 1
        · exact ⟨false, Subtype.ext (by simp [f, hq1])⟩
        · exact ⟨true, Subtype.ext (by simp [f, (h q hq hq1)])⟩
      simpa using Nat.card_le_card_of_surjective f hf
    omega

  have hcomm : ∃ q : G, q ∈ (Q : Subgroup G) ∧ q ≠ 1 ∧ q * c * q⁻¹ = c := by
    rcases hconj q₁ with h1 | h1
    · exact ⟨q₁, hq₁Q, hq₁, h1⟩
    rcases hconj q₂ with h2 | h2
    · exact ⟨q₂, hq₂Q, hq₂, h2⟩
    refine ⟨q₁ * q₂, (Q : Subgroup G).mul_mem hq₁Q hq₂Q, ?_, ?_⟩
    · intro h
      apply hq₂₁
      have hq1sq := hQexp q₁ hq₁Q
      calc q₂ = q₁ ^ 2 * q₂ := by rw [hq1sq, one_mul]
        _ = q₁ * (q₁ * q₂) := by rw [sq, mul_assoc]
        _ = q₁ := by rw [h, mul_one]
    · have hc3 : c ^ 3 = 1 := by rw [← hoc]; exact pow_orderOf_eq_one c
      calc q₁ * q₂ * c * (q₁ * q₂)⁻¹ = q₁ * (q₂ * c * q₂⁻¹) * q₁⁻¹ := by group
        _ = q₁ * c ^ 2 * q₁⁻¹ := by rw [h2]
        _ = (q₁ * c * q₁⁻¹) ^ 2 := by simp only [sq]; group
        _ = (c ^ 2) ^ 2 := by rw [h1]
        _ = c * c ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = c := by rw [hc3, mul_one]
  obtain ⟨q, hqQ, hq1, hqc⟩ := hcomm
  have hoq : orderOf q = 2 := orderOf_eq_two_of_sq (hQexp q hqQ) hq1
  exact not_commute hexp hoq hoc (by
    rw [commute_iff_eq]
    calc q * c = q * c * q⁻¹ * q := by group
      _ = c * q := by rw [hqc])

end
end Dubon2026.SourceOrderTwelve

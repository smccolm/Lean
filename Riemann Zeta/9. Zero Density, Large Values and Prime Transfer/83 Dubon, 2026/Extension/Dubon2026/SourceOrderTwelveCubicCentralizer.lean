import Dubon2026.SourceOrderTwelveInvolutionConjugacy

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

theorem mem_zpowers_of_mul_eq_mul {b x : G} (hb : orderOf b = 3) (h : x * b = b * x) :
    x ∈ Subgroup.zpowers b := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hxC : x ∈ C := by rw [hC, Subgroup.mem_centralizer_singleton_iff]; exact h
  have hbC : b ∈ C := by rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hpC : IsPGroup 3 C := by
    intro k
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hk : (k : G) * b = b * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    have hk3 : orderOf (k : G) ≠ 2 := fun h2 => not_commute hexp h2 hb hk
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rcases orderOf_cases hexp (k : G) with h1 | h1 | h1
    · rw [orderOf_eq_one_iff.mp h1, one_pow]
    · exact absurd h1 hk3
    · rw [← h1, pow_orderOf_eq_one]
  obtain ⟨P, hCP⟩ := hpC.exists_le_sylow
  have hb1 : b ≠ 1 := by intro h1; rw [h1, orderOf_one] at hb; norm_num at hb
  rw [zpowers_eq_of_mem (card_sylow_three hG P) (hCP hbC) hb1]
  exact hCP hxC

theorem conj_ne_sq {c z : G} (hc : orderOf c = 3) : z⁻¹ * c * z ≠ c ^ 2 := by
  intro h
  have hc3 : c ^ 3 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by intro h1; rw [h1, orderOf_one] at hc; norm_num at hc
  have hcc : c ≠ c ^ 2 := by
    intro h2; apply hc1
    have h2' : c * c = c := by rw [← sq]; exact h2.symm
    calc c = c * c * c⁻¹ := by group
      _ = 1 := by rw [h2']; group
  rcases orderOf_cases hexp z with hz | hz | hz
  · rw [orderOf_eq_one_iff.mp hz] at h
    apply hcc; simpa using h
  ·
    have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have hzi : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
    rw [hzi] at h
    have hzc : (z * c) ^ 2 = 1 := by
      calc (z * c) ^ 2 = z * c * z * c := by simp only [sq]; group
        _ = c ^ 2 * c := by rw [h]
        _ = 1 := by rw [← pow_succ, hc3]
    have hc2 : c ^ 2 = 1 := by
      have := sq_mul_eq_one hG hexp hz2 hzc
      calc c ^ 2 = (z * (z * c)) ^ 2 := by rw [← mul_assoc, ← sq, hz2, one_mul]
        _ = 1 := this
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  ·
    have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have h2 : (z ^ 2)⁻¹ * c * z ^ 2 = c := by
      calc (z ^ 2)⁻¹ * c * z ^ 2 = z⁻¹ * (z⁻¹ * c * z) * z := by simp only [sq]; group
        _ = z⁻¹ * c ^ 2 * z := by rw [h]
        _ = (z⁻¹ * c * z) ^ 2 := by simp only [sq]; group
        _ = (c ^ 2) ^ 2 := by rw [h]
        _ = c ^ 3 * c := by simp only [pow_succ, pow_zero, one_mul]; group
        _ = c := by rw [hc3, one_mul]
    have hzz : z ^ 2 = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hz3]
    rw [hzz, inv_inv] at h2

    have : z⁻¹ * c * z = c := by
      calc z⁻¹ * c * z = z⁻¹ * (z * c * z⁻¹) * z := by rw [h2]
        _ = c := by group
    rw [this] at h
    exact hcc h

end
end Dubon2026.SourceOrderTwelve

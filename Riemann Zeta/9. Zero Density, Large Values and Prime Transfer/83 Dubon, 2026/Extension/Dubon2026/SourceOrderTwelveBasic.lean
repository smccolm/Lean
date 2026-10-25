import Mathlib

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

theorem factorization_twelve_three : (12 : ℕ).factorization 3 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have : (12 : ℕ) = 3 ^ 1 * 4 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twelve_two : (12 : ℕ).factorization 2 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

section Structure

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)

include hexp in
omit [Finite G] in
theorem orderOf_cases (g : G) : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  rcases hexp g with h | h
  · have hd := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases (orderOf g) <;> simp_all
  · have hd := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases (orderOf g) <;> simp_all

include hexp in

omit [Finite G] in
theorem not_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 3) : ¬Commute a b := by
  intro h
  have h6 : orderOf (a * b) = 6 := by
    rw [h.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; norm_num), ha, hb]
  rcases orderOf_cases hexp (a * b) with h1 | h1 | h1 <;> omega

omit [Finite G] in
theorem orderOf_eq_two_of_sq {a : G} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime ha ha1

omit [Finite G] in
theorem orderOf_eq_three_of_cube {b : G} (hb : b ^ 3 = 1) (hb1 : b ≠ 1) : orderOf b = 3 :=
  orderOf_eq_prime hb hb1

include hexp in
omit [Finite G] in
theorem sq_eq_one_of_orderOf_ne_three {g : G} (h : orderOf g ≠ 3) : g ^ 2 = 1 := by
  rcases orderOf_cases hexp g with h1 | h1 | h1
  · rw [orderOf_eq_one_iff.mp h1, one_pow]
  · rw [← h1, pow_orderOf_eq_one]
  · exact absurd h1 h

include hG in
theorem card_sylow_three (P : Sylow 3 G) : Nat.card (P : Subgroup G) = 3 := by
  rw [Sylow.card_eq_multiplicity, hG, factorization_twelve_three, pow_one]

include hG in
theorem card_sylow_two (Q : Sylow 2 G) : Nat.card (Q : Subgroup G) = 4 := by
  rw [Sylow.card_eq_multiplicity, hG, factorization_twelve_two]; norm_num

omit [Finite G] in
theorem orderOf_eq_three_of_mem {H : Subgroup G} (hH : Nat.card H = 3) {g : G} (hg : g ∈ H)
    (hg1 : g ≠ 1) : orderOf g = 3 := by
  have hd : orderOf g ∣ 3 := hH ▸ Subgroup.orderOf_dvd_natCard H hg
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · exact h

omit [Finite G] in
theorem zpowers_eq_of_mem {H : Subgroup G} (hH : Nat.card H = 3) {g : G} (hg : g ∈ H) (hg1 : g ≠ 1) :
    Subgroup.zpowers g = H := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact hg
  · rw [hH, Nat.card_zpowers, orderOf_eq_three_of_mem hH hg hg1]

omit [Finite G] in
theorem mem_of_card_three {H : Subgroup G} (hH : Nat.card H = 3) {c : G} (hc : c ∈ H) (hc1 : c ≠ 1)
    {g : G} (hg : g ∈ H) : g = 1 ∨ g = c ∨ g = c ^ 2 := by
  have hoc := orderOf_eq_three_of_mem hH hc hc1
  rw [← zpowers_eq_of_mem hH hc hc1, Subgroup.mem_zpowers_iff] at hg
  obtain ⟨k, rfl⟩ := hg
  rw [← zpow_mod_orderOf, hoc]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right; norm_cast

end Structure

end
end Dubon2026.SourceOrderTwelve

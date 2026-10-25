import Dubon2026.SourceOrderTwelveElementCounts

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

theorem mem_iff_sq_eq_one_of_card_eq_four {H : Subgroup G} (hH : Nat.card H = 4) (g : G) :
    g ∈ H ↔ g ^ 2 = 1 := by
  have hsub : (H : Set G) ⊆ {g : G | g ^ 2 = 1} := by
    intro h hh
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro h3
    have : orderOf h ∣ 4 := hH ▸ Subgroup.orderOf_dvd_natCard H hh
    rw [h3] at this; norm_num at this
  have heq : (H : Set G) = {g : G | g ^ 2 = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [ncard_sq_eq_one hG hexp, ← Nat.card_coe_set_eq]
      exact hH.symm.le) (Set.toFinite _)
  rw [← SetLike.mem_coe, heq]; rfl

theorem sq_mul_eq_one {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) : (x * y) ^ 2 = 1 := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hQ := card_sylow_two hG Q
  rw [← mem_iff_sq_eq_one_of_card_eq_four hG hexp hQ] at hx hy ⊢
  exact (Q : Subgroup G).mul_mem hx hy

theorem mul_eq_mul_iff_sq_eq_one {a : G} (ha : orderOf a = 2) (x : G) : x * a = a * x ↔ x ^ 2 = 1 := by
  constructor
  · intro h
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro hx
    exact not_commute hexp ha hx h.symm
  · intro hx
    have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
    have hxa := sq_mul_eq_one hG hexp hx ha2

    have h1 : x * a = (x * a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← sq, hxa]
    have h2 : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, hx]
    have h3 : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
    rw [h1, mul_inv_rev, h2, h3]

theorem exists_conj_eq {a τ : G} (ha : orderOf a = 2) (hτ : orderOf τ = 2) : ∃ x : G, x⁻¹ * a * x = τ := by
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  have hb3 : b ^ 3 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hτ1 : τ ≠ 1 := by intro h; rw [h, orderOf_one] at hτ; norm_num at hτ
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ, pow_orderOf_eq_one]

  set a₁ := b⁻¹ * a * b with ha₁
  set a₂ := (b ^ 2)⁻¹ * a * b ^ 2 with ha₂
  have hb2 : orderOf (b ^ 2) = 3 := by
    apply orderOf_eq_three_of_cube
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hb3, one_pow]
    · intro h
      have : b = 1 := by
        calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
          _ = 1 := by rw [hb3, h]; group
      rw [this, orderOf_one] at hb; norm_num at hb
  have hne01 : a ≠ a₁ := by
    intro h
    apply not_commute hexp ha hb
    rw [commute_iff_eq]
    calc a * b = b * (b⁻¹ * a * b) := by group
      _ = b * a := by rw [← ha₁, ← h]
  have hne02 : a ≠ a₂ := by
    intro h
    apply not_commute hexp ha hb2
    rw [commute_iff_eq]
    calc a * b ^ 2 = b ^ 2 * ((b ^ 2)⁻¹ * a * b ^ 2) := by group
      _ = b ^ 2 * a := by rw [← ha₂, ← h]
  have hne12 : a₁ ≠ a₂ := by
    intro h
    apply hne01
    calc a = b * a₁ * b⁻¹ := by rw [ha₁]; group
      _ = b * a₂ * b⁻¹ := by rw [h]
      _ = a₁ := by rw [ha₂, ha₁]; simp only [sq]; group
  have ha2' : a * a = 1 := by rw [← sq]; exact ha2
  have hsq₁ : a₁ ^ 2 = 1 := by
    rw [ha₁]
    calc (b⁻¹ * a * b) ^ 2 = b⁻¹ * (a * a) * b := by simp only [sq]; group
    _ = 1 := by rw [ha2']; group
  have hsq₂ : a₂ ^ 2 = 1 := by
    rw [ha₂]
    calc ((b ^ 2)⁻¹ * a * b ^ 2) ^ 2 = (b ^ 2)⁻¹ * (a * a) * b ^ 2 := by simp only [sq]; group
    _ = 1 := by rw [ha2']; group
  have h1₁ : a₁ ≠ 1 := by
    intro h; apply ha1
    calc a = b * a₁ * b⁻¹ := by rw [ha₁]; group
      _ = 1 := by rw [h]; group
  have h1₂ : a₂ ≠ 1 := by
    intro h; apply ha1
    calc a = b ^ 2 * a₂ * (b ^ 2)⁻¹ := by rw [ha₂]; group
      _ = 1 := by rw [h]; group

  have hsub : ({1, a, a₁, a₂} : Set G) ⊆ {g : G | g ^ 2 = 1} := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simp
    · exact ha2
    · exact hsq₁
    · exact hsq₂
  have hcard : ({1, a, a₁, a₂} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm h1₁, Ne.symm h1₂]),
      Set.ncard_insert_of_notMem (by simp [hne01, hne02]),
      Set.ncard_pair hne12]
  have heq : ({1, a, a₁, a₂} : Set G) = {g : G | g ^ 2 = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_sq_eq_one hG hexp, hcard]) (Set.toFinite _)
  have hτmem : τ ∈ ({1, a, a₁, a₂} : Set G) := by rw [heq]; exact hτ2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτmem
  rcases hτmem with h | h | h | h
  · exact absurd h hτ1
  · exact ⟨1, by rw [h]; group⟩
  · exact ⟨b, by rw [h, ha₁]⟩
  · exact ⟨b ^ 2, by rw [h, ha₂]⟩

end
end Dubon2026.SourceOrderTwelve

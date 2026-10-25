import Dubon2026.SourceOrderTwelveSylowNonNormal

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

theorem card_sylow_three_eq_four : Nat.card (Sylow 3 G) = 4 := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h1 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have h2 : Nat.card (Sylow 3 G) ∣ (P : Subgroup G).index := P.card_dvd_index
  have hidx : (P : Subgroup G).index = 4 := by
    have := (P : Subgroup G).index_mul_card
    rw [hG, card_sylow_three hG P] at this
    omega
  rw [hidx] at h2
  have hne : Nat.card (Sylow 3 G) ≠ 1 := by
    intro h
    apply sylow_three_not_normal hG hexp P
    have h' := Sylow.card_eq_index_normalizer P
    rw [h] at h'
    exact Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h'.symm)
  have hle : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
  interval_cases h : (Nat.card (Sylow 3 G))
  · norm_num at h2
  · exact absurd rfl hne
  · exact absurd h1 (by decide)
  · norm_num at h2
  · rfl

omit hG hexp in
omit [Finite G] in
theorem exists_sylow_mem_of_orderOf {g : G} (hg : orderOf g = 3) : ∃ P : Sylow 3 G, g ∈ (P : Subgroup G) := by
  have : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨P, hP⟩ := this.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers g)⟩

omit hexp in
theorem sylow_eq_of_mem {g : G} (hg1 : g ≠ 1) {P P' : Sylow 3 G} (h : g ∈ (P : Subgroup G))
    (h' : g ∈ (P' : Subgroup G)) : P = P' := by
  apply Sylow.ext
  rw [← zpowers_eq_of_mem (card_sylow_three hG P) h hg1, ← zpowers_eq_of_mem (card_sylow_three hG P') h' hg1]

omit hG hexp in
omit [Finite G] in
theorem heq_subtype_of_sylow_eq {P₁ P₂ : Sylow 3 G} (h : P₁ = P₂) {g : G}
    (h₁ : g ∈ (P₁ : Subgroup G) ∧ g ≠ 1) (h₂ : g ∈ (P₂ : Subgroup G) ∧ g ≠ 1) :
    HEq (⟨g, h₁⟩ : {g : G // g ∈ (P₁ : Subgroup G) ∧ g ≠ 1})
      (⟨g, h₂⟩ : {g : G // g ∈ (P₂ : Subgroup G) ∧ g ≠ 1}) := by
  subst h; rfl

theorem ncard_orderOf_eq_three : {g : G | orderOf g = 3}.ncard = 8 := by
  classical
  letI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hne : ∀ {g : G}, orderOf g = 3 → g ≠ 1 := by
    intro g hg h; rw [h, orderOf_one] at hg; norm_num at hg
  let Pof : {g : G | orderOf g = 3} → Sylow 3 G := fun g => (exists_sylow_mem_of_orderOf g.2).choose
  have hPof : ∀ g : {g : G | orderOf g = 3}, (g : G) ∈ (Pof g : Subgroup G) := fun g =>
    (exists_sylow_mem_of_orderOf g.2).choose_spec
  have e : {g : G | orderOf g = 3} ≃ Σ P : Sylow 3 G, {g : G // g ∈ (P : Subgroup G) ∧ g ≠ 1} :=
    { toFun := fun g => ⟨Pof g, ⟨g.1, hPof g, hne g.2⟩⟩
      invFun := fun x => ⟨x.2.1, orderOf_eq_three_of_mem (card_sylow_three hG x.1) x.2.2.1 x.2.2.2⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := by
        rintro ⟨P, g, hgP, hg1⟩
        have hP : Pof ⟨g, orderOf_eq_three_of_mem (card_sylow_three hG P) hgP hg1⟩ = P :=
          sylow_eq_of_mem hG hg1 (hPof _) hgP
        exact Sigma.ext hP (heq_subtype_of_sylow_eq hP _ _) }
  have h2 : ∀ P : Sylow 3 G, Nat.card {g : G // g ∈ (P : Subgroup G) ∧ g ≠ 1} = 2 := by
    intro P
    have hs : {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} = ((P : Subgroup G) : Set G) \ {1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
    have h3 : (((P : Subgroup G) : Set G)).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]; exact card_sylow_three hG P
    have := Set.ncard_diff_singleton_of_mem (show (1 : G) ∈ ((P : Subgroup G) : Set G) from
      (P : Subgroup G).one_mem)
    rw [h3] at this
    change Nat.card ({g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} : Set G) = 2
    rw [Nat.card_coe_set_eq, hs, this]
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_sylow_three_eq_four hG hexp]

theorem ncard_sq_eq_one : {g : G | g ^ 2 = 1}.ncard = 4 := by
  have hunion : {g : G | g ^ 2 = 1} ∪ {g | orderOf g = 3} = Set.univ := by
    ext g
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : orderOf g = 3
    · exact Or.inr h
    · exact Or.inl (sq_eq_one_of_orderOf_ne_three hexp h)
  have hdisj : Disjoint {g : G | g ^ 2 = 1} {g | orderOf g = 3} := by
    rw [Set.disjoint_left]
    intro g h1 h2
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h2] at this
    norm_num at this
  have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  rw [hunion, Set.ncard_univ, hG, ncard_orderOf_eq_three hG hexp] at h
  omega

end
end Dubon2026.SourceOrderTwelve

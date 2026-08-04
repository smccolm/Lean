import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Metric

namespace RiemannZeta.GuthMaynard

def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y

def SeparatedSelectionHypothesis : Prop :=
  ∀ (S : Finset ℝ) (L : ℕ),
    (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) →
    ∃ W ⊆ S, RiemannZeta.GuthMaynard.IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card

open scoped Classical

theorem separated_selection : SeparatedSelectionHypothesis := by
  intro S L hL
  let S_even := S.filter (fun t => Even ⌊t⌋)
  let S_odd := S.filter (fun t => Odd ⌊t⌋)
  have H : S_even ∪ S_odd = S := by
    ext a
    dsimp [S_even, S_odd]
    simp only [Finset.mem_union, Finset.mem_filter]
    have : Even ⌊a⌋ ∨ Odd ⌊a⌋ := Int.even_or_odd ⌊a⌋
    tauto
  have H_card : S_even.card + S_odd.card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    · rw [H]
    · rw [Finset.disjoint_filter]
      intro x hx h_even h_odd
      rcases h_even with ⟨k, hk⟩
      rcases h_odd with ⟨m, hm⟩
      omega


  have H_L : ∀ z : ℤ, (S.filter (fun t => ⌊t⌋ = z)).card ≤ L := by
    intro z
    have := hL z
    have H_eq : (S.filter (fun t => ⌊t⌋ = z)) = S.filter (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1) := by
      ext a
      simp only [Finset.mem_filter]
      apply and_congr_right'
      exact Int.floor_eq_iff
    rw [H_eq]
    exact this
  have H_card_le : S.card ≤ 2 * S_even.card ∨ S.card ≤ 2 * S_odd.card := by
    omega

  let g_even (z : ℤ) : ℝ :=
    if h : (S_even.filter (fun t => ⌊t⌋ = z)).Nonempty then
      (S_even.filter (fun t => ⌊t⌋ = z)).max' h
    else
      0

  let W_even := (S_even.image (fun t => ⌊t⌋)).image g_even

  have W_even_sub_S : W_even ⊆ S := by
    intro x hx
    have hx2 : x ∈ (S_even.image (fun t => ⌊t⌋)).image g_even := hx
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨z, hz, rfl⟩
    rw [Finset.mem_image] at hz
    rcases hz with ⟨t, ht, rfl⟩
    dsimp [g_even]
    split
    · case isTrue h =>
      have H_max := Finset.max'_mem _ h
      simp only [Finset.mem_filter] at H_max
      have ht_in : t ∈ S := by
        have : t ∈ S_even := ht
        simp only [Finset.mem_filter, S_even] at this
        exact this.1
      have H_max_in : (S_even.filter (fun t_1 => ⌊t_1⌋ = ⌊t⌋)).max' h ∈ S_even := by
        have H_max2 := Finset.max'_mem _ h
        simp only [Finset.mem_filter] at H_max2
        exact H_max2.1
      simp only [Finset.mem_filter, S_even] at H_max_in
      exact H_max_in.1
    · case isFalse h =>
      have H_nonempty : (S_even.filter (fun t' => ⌊t'⌋ = ⌊t⌋)).Nonempty := by
        use t
        rw [Finset.mem_filter]
        exact ⟨ht, rfl⟩
      contradiction

  have g_even_floor : ∀ z ∈ S_even.image (fun t => ⌊t⌋), ⌊g_even z⌋ = z := by
    intro z hz
    dsimp [g_even]
    have H_nonempty : (S_even.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      rw [Finset.mem_image] at hz
      rcases hz with ⟨t, ht, rfl⟩
      use t
      rw [Finset.mem_filter]
      exact ⟨ht, rfl⟩
    split
    · case isTrue h =>
      have H_max := Finset.max'_mem _ h
      simp only [Finset.mem_filter] at H_max
      exact H_max.2
    · case isFalse h =>
      contradiction

  have H_floor : ∀ x ∈ W_even, ⌊x⌋ ∈ S_even.image (fun t => ⌊t⌋) ∧ x = g_even ⌊x⌋ := by
    intro x hx
    have hx2 : x ∈ (S_even.image (fun t => ⌊t⌋)).image g_even := hx
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨z, hz, rfl⟩
    have hz2 : ⌊g_even z⌋ = z := g_even_floor z hz
    rw [hz2]
    exact ⟨hz, rfl⟩

  have W_even_sep : RiemannZeta.GuthMaynard.IsSeparated 1 W_even := by
    intro x hx y hy hxy
    have hx_fl := H_floor x hx
    have hy_fl := H_floor y hy
    have hx_even : Even ⌊x⌋ := by
      have h1 := hx_fl.1
      simp only [Finset.mem_image, Finset.mem_filter, S_even] at h1
      rcases h1 with ⟨t, ht, ht2⟩
      rw [← ht2]
      exact ht.2
    have hy_even : Even ⌊y⌋ := by
      have h1 := hy_fl.1
      simp only [Finset.mem_image, Finset.mem_filter, S_even] at h1
      rcases h1 with ⟨t, ht, ht2⟩
      rw [← ht2]
      exact ht.2
    have h_neq : ⌊x⌋ ≠ ⌊y⌋ := by
      intro hc
      have : x = y := by
        rw [hx_fl.2, hy_fl.2, hc]
      exact hxy this
    have hx_bounds : (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 := by
      exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
    have hy_bounds : (⌊y⌋ : ℝ) ≤ y ∧ y < (⌊y⌋ : ℝ) + 1 := by
      exact ⟨Int.floor_le y, Int.lt_floor_add_one y⟩
    dsimp [dist]
    cases le_total ⌊x⌋ ⌊y⌋ with
    | inl hle =>
      have H_le : ⌊y⌋ - ⌊x⌋ ≥ 2 := by
        rcases hx_even with ⟨k, hk⟩
        rcases hy_even with ⟨m, hm⟩
        omega
      have : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) ≥ 2 := by exact_mod_cast H_le
      have H_yx : y - x ≥ 1 := by linarith
      have H_abs : y - x ≤ |x - y| := by
        rw [abs_sub_comm]
        exact le_abs_self (y - x)
      linarith
    | inr hle =>
      have H_le : ⌊x⌋ - ⌊y⌋ ≥ 2 := by
        rcases hx_even with ⟨k, hk⟩
        rcases hy_even with ⟨m, hm⟩
        omega
      have : (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) ≥ 2 := by exact_mod_cast H_le
      have H_xy : x - y ≥ 1 := by linarith
      have H_abs : x - y ≤ |x - y| := by
        exact le_abs_self (x - y)
      linarith

  have W_even_card : W_even.card = (S_even.image (fun t => ⌊t⌋)).card := by
    apply Finset.card_image_of_injOn
    intro z1 hz1 z2 hz2 hz
    have hz1_eq := g_even_floor z1 hz1
    have hz2_eq := g_even_floor z2 hz2
    rw [hz] at hz1_eq
    rw [← hz2_eq, hz1_eq]

  have S_even_card_le : S_even.card ≤ L * W_even.card := by
    have eq1 : S_even = (S_even.image (fun t => ⌊t⌋)).biUnion (fun z => S_even.filter (fun t => ⌊t⌋ = z)) := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      constructor
      · intro ha
        use ⌊a⌋
        exact ⟨⟨a, ha, rfl⟩, ha, rfl⟩
      · rintro ⟨z, ⟨_, _, rfl⟩, ha, eq⟩
        exact ha
    have eq2 : S_even.card = ∑ z ∈ S_even.image (fun t => ⌊t⌋), (S_even.filter (fun t => ⌊t⌋ = z)).card := by
      nth_rw 1 [eq1]
      apply Finset.card_biUnion
      intro x hx y hy hxy
      simp only [Finset.disjoint_filter]
      intro a ha hax hay
      rw [hax] at hay
      exact hxy hay
    rw [W_even_card]
    rw [eq2]
    have eq3 : ∑ z ∈ S_even.image (fun t => ⌊t⌋), (S_even.filter (fun t => ⌊t⌋ = z)).card ≤ ∑ z ∈ S_even.image (fun t => ⌊t⌋), L := by
      apply Finset.sum_le_sum
      intro i hi
      have H_L_i := H_L i
      have sub_S : S_even.filter (fun t => ⌊t⌋ = i) ⊆ S.filter (fun t => ⌊t⌋ = i) := by
        intro t ht
        simp only [Finset.mem_filter] at ht ⊢
        exact ⟨(Finset.mem_filter.mp ht.1).1, ht.2⟩
      exact le_trans (Finset.card_le_card sub_S) H_L_i
    have eq4 : ∑ z ∈ S_even.image (fun t => ⌊t⌋), L = L * (S_even.image (fun t => ⌊t⌋)).card := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring
    rw [eq4] at eq3
    exact eq3

  let g_odd (z : ℤ) : ℝ :=
    if h : (S_odd.filter (fun t => ⌊t⌋ = z)).Nonempty then
      (S_odd.filter (fun t => ⌊t⌋ = z)).max' h
    else
      0

  let W_odd := (S_odd.image (fun t => ⌊t⌋)).image g_odd

  have W_odd_sub_S : W_odd ⊆ S := by
    intro x hx
    have hx2 : x ∈ (S_odd.image (fun t => ⌊t⌋)).image g_odd := hx
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨z, hz, rfl⟩
    rw [Finset.mem_image] at hz
    rcases hz with ⟨t, ht, rfl⟩
    dsimp [g_odd]
    split
    · case isTrue h =>
      have H_max := Finset.max'_mem _ h
      simp only [Finset.mem_filter] at H_max
      have ht_in : t ∈ S := by
        have : t ∈ S_odd := ht
        simp only [Finset.mem_filter, S_odd] at this
        exact this.1
      have H_max_in : (S_odd.filter (fun t_1 => ⌊t_1⌋ = ⌊t⌋)).max' h ∈ S_odd := by
        have H_max2 := Finset.max'_mem _ h
        simp only [Finset.mem_filter] at H_max2
        exact H_max2.1
      simp only [Finset.mem_filter, S_odd] at H_max_in
      exact H_max_in.1
    · case isFalse h =>
      have H_nonempty : (S_odd.filter (fun t' => ⌊t'⌋ = ⌊t⌋)).Nonempty := by
        use t
        rw [Finset.mem_filter]
        exact ⟨ht, rfl⟩
      contradiction

  have g_odd_floor : ∀ z ∈ S_odd.image (fun t => ⌊t⌋), ⌊g_odd z⌋ = z := by
    intro z hz
    dsimp [g_odd]
    have H_nonempty : (S_odd.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      rw [Finset.mem_image] at hz
      rcases hz with ⟨t, ht, rfl⟩
      use t
      rw [Finset.mem_filter]
      exact ⟨ht, rfl⟩
    split
    · case isTrue h =>
      have H_max := Finset.max'_mem _ h
      simp only [Finset.mem_filter] at H_max
      exact H_max.2
    · case isFalse h =>
      contradiction

  have H_floor_odd : ∀ x ∈ W_odd, ⌊x⌋ ∈ S_odd.image (fun t => ⌊t⌋) ∧ x = g_odd ⌊x⌋ := by
    intro x hx
    have hx2 : x ∈ (S_odd.image (fun t => ⌊t⌋)).image g_odd := hx
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨z, hz, rfl⟩
    have hz2 : ⌊g_odd z⌋ = z := g_odd_floor z hz
    rw [hz2]
    exact ⟨hz, rfl⟩

  have W_odd_sep : RiemannZeta.GuthMaynard.IsSeparated 1 W_odd := by
    intro x hx y hy hxy
    have hx_fl := H_floor_odd x hx
    have hy_fl := H_floor_odd y hy
    have hx_odd : Odd ⌊x⌋ := by
      have h1 := hx_fl.1
      simp only [Finset.mem_image, Finset.mem_filter, S_odd] at h1
      rcases h1 with ⟨t, ht, ht2⟩
      rw [← ht2]
      exact ht.2
    have hy_odd : Odd ⌊y⌋ := by
      have h1 := hy_fl.1
      simp only [Finset.mem_image, Finset.mem_filter, S_odd] at h1
      rcases h1 with ⟨t, ht, ht2⟩
      rw [← ht2]
      exact ht.2
    have h_neq : ⌊x⌋ ≠ ⌊y⌋ := by
      intro hc
      have : x = y := by
        rw [hx_fl.2, hy_fl.2, hc]
      exact hxy this
    have hx_bounds : (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 := by
      exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
    have hy_bounds : (⌊y⌋ : ℝ) ≤ y ∧ y < (⌊y⌋ : ℝ) + 1 := by
      exact ⟨Int.floor_le y, Int.lt_floor_add_one y⟩
    dsimp [dist]
    cases le_total ⌊x⌋ ⌊y⌋ with
    | inl hle =>
      have H_le : ⌊y⌋ - ⌊x⌋ ≥ 2 := by
        rcases hx_odd with ⟨k, hk⟩
        rcases hy_odd with ⟨m, hm⟩
        omega
      have : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) ≥ 2 := by exact_mod_cast H_le
      have H_yx : y - x ≥ 1 := by linarith
      have H_abs : y - x ≤ |x - y| := by
        rw [abs_sub_comm]
        exact le_abs_self (y - x)
      linarith
    | inr hle =>
      have H_le : ⌊x⌋ - ⌊y⌋ ≥ 2 := by
        rcases hx_odd with ⟨k, hk⟩
        rcases hy_odd with ⟨m, hm⟩
        omega
      have : (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) ≥ 2 := by exact_mod_cast H_le
      have H_xy : x - y ≥ 1 := by linarith
      have H_abs : x - y ≤ |x - y| := by
        exact le_abs_self (x - y)
      linarith

  have W_odd_card : W_odd.card = (S_odd.image (fun t => ⌊t⌋)).card := by
    apply Finset.card_image_of_injOn
    intro z1 hz1 z2 hz2 hz
    have hz1_eq := g_odd_floor z1 hz1
    have hz2_eq := g_odd_floor z2 hz2
    rw [hz] at hz1_eq
    rw [← hz2_eq, hz1_eq]

  have S_odd_card_le : S_odd.card ≤ L * W_odd.card := by
    have eq1 : S_odd = (S_odd.image (fun t => ⌊t⌋)).biUnion (fun z => S_odd.filter (fun t => ⌊t⌋ = z)) := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      constructor
      · intro ha
        use ⌊a⌋
        exact ⟨⟨a, ha, rfl⟩, ha, rfl⟩
      · rintro ⟨z, ⟨_, _, rfl⟩, ha, eq⟩
        exact ha
    have eq2 : S_odd.card = ∑ z ∈ S_odd.image (fun t => ⌊t⌋), (S_odd.filter (fun t => ⌊t⌋ = z)).card := by
      nth_rw 1 [eq1]
      apply Finset.card_biUnion
      intro x hx y hy hxy
      simp only [Finset.disjoint_filter]
      intro a ha hax hay
      rw [hax] at hay
      exact hxy hay
    rw [W_odd_card]
    rw [eq2]
    have eq3 : ∑ z ∈ S_odd.image (fun t => ⌊t⌋), (S_odd.filter (fun t => ⌊t⌋ = z)).card ≤ ∑ z ∈ S_odd.image (fun t => ⌊t⌋), L := by
      apply Finset.sum_le_sum
      intro i hi
      have H_L_i := H_L i
      have sub_S : S_odd.filter (fun t => ⌊t⌋ = i) ⊆ S.filter (fun t => ⌊t⌋ = i) := by
        intro t ht
        simp only [Finset.mem_filter] at ht ⊢
        exact ⟨(Finset.mem_filter.mp ht.1).1, ht.2⟩
      exact le_trans (Finset.card_le_card sub_S) H_L_i
    have eq4 : ∑ z ∈ S_odd.image (fun t => ⌊t⌋), L = L * (S_odd.image (fun t => ⌊t⌋)).card := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring
    rw [eq4] at eq3
    exact eq3

  cases H_card_le with
  | inl h_even =>
    use W_even
    constructor
    · exact W_even_sub_S
    · constructor
      · exact W_even_sep
      · have : S.card ≤ 2 * (L * W_even.card) := by
          calc S.card ≤ 2 * S_even.card := h_even
          _ ≤ 2 * (L * W_even.card) := by omega
        have H_mul : 2 * (L * W_even.card) = 2 * L * W_even.card := by ring
        rw [H_mul] at this
        exact this
  | inr h_odd =>
    use W_odd
    constructor
    · exact W_odd_sub_S
    · constructor
      · exact W_odd_sep
      · have : S.card ≤ 2 * (L * W_odd.card) := by
          calc S.card ≤ 2 * S_odd.card := h_odd
          _ ≤ 2 * (L * W_odd.card) := by omega
        have H_mul : 2 * (L * W_odd.card) = 2 * L * W_odd.card := by ring
        rw [H_mul] at this
        exact this







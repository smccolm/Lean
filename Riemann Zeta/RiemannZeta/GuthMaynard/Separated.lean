import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Metric

namespace RiemannZeta.GuthMaynard

/-- A finite set `W` of real numbers is `δ`-separated if the distance between any two distinct points is at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y

lemma card_pos_of_nonempty {α : Type*} (W : Finset α) (h : W.Nonempty) : 0 < W.card := by
  exact Finset.card_pos.mpr h

/-- 
The exact interval used in the zero-density theorem (Section 13.1) dyadic decomposition:
points lie in `[T, 2 * T]`.
-/
def InTargetInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc T (2 * T)

/-- The interval for the basic Large Values Estimate (Theorem 1.1) is `[0, T]`. -/
def InBaseInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc 0 T

/-- 
Translation of a finite set by a constant `c`. 
This is used in Phase 4 to map `[T, 2T]` to `[0, T]`.
-/
noncomputable def translateSet (c : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => x - c)

theorem isSeparated_translate (δ c : ℝ) (W : Finset ℝ) (h : IsSeparated δ W) : 
    IsSeparated δ (translateSet c W) := by
  intro x hx y hy hxy
  rw [translateSet, Finset.mem_image] at hx hy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  have hx'y' : x' ≠ y' := by
    intro hc
    rw [hc] at hxy
    exact hxy rfl
  have hd : dist (x' - c) (y' - c) = dist x' y' := by
    dsimp [dist]
    congr 1
    ring
  rw [hd]
  exact h x' hx' y' hy' hx'y'

theorem inBaseInterval_translate (T : ℝ) (W : Finset ℝ) (h : InTargetInterval T W) :
    InBaseInterval T (translateSet T W) := by
  intro x hx
  rw [translateSet, Finset.mem_image] at hx
  rcases hx with ⟨x', hx', rfl⟩
  have hT := h x' hx'
  rw [mem_Icc] at hT ⊢
  constructor
  · linarith [hT.1]
  · linarith [hT.2]

theorem translateSet_card (c : ℝ) (W : Finset ℝ) : (translateSet c W).card = W.card := by
  unfold translateSet
  apply Finset.card_image_of_injective
  intro x y hxy
  change x - c = y - c at hxy
  have h1 : x - c + c = y - c + c := by rw [hxy]
  ring_nf at h1
  exact h1

/-- 
Combinatorial separation extraction hypothesis. 
States that from any finite set S where local occupancy in [x, x+1) is bounded by L,
we can extract a 1-separated subset W whose size is proportional to S.
Isolated as a hypothesis pending a full Lean combinatorial proof.
-/
def SeparatedSelectionProp : Prop :=
  ∀ (S : Finset ℝ) (L : ℕ),
    (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) →
    ∃ W ⊆ S, RiemannZeta.GuthMaynard.IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card

open scoped Classical

theorem separated_selection : SeparatedSelectionProp := by
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

/-- Weighted local-occupancy form of finite one-dimensional separated selection. -/
def WeightedSeparatedSelectionProp : Prop :=
  ∀ (S : Finset ℝ) (weight : ℝ → ℕ) (L : ℕ),
    (∀ (z : ℤ),
      ∑ t ∈ S.filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1), weight t ≤ L) →
    ∃ W ⊆ S, RiemannZeta.GuthMaynard.IsSeparated 1 W ∧
      ∑ t ∈ S, weight t ≤ 2 * L * W.card

/--
Choose one representative from every occupied even or odd unit bin, selecting
the parity class carrying at least half of the total weight.
-/
theorem weighted_separated_selection : WeightedSeparatedSelectionProp := by
  intro S weight L hL
  let S_even := S.filter (fun t => Even ⌊t⌋)
  let S_odd := S.filter (fun t => Odd ⌊t⌋)
  have hDisjoint : Disjoint S_even S_odd := by
    rw [Finset.disjoint_filter]
    intro x hx hEven hOdd
    rcases hEven with ⟨k, hk⟩
    rcases hOdd with ⟨m, hm⟩
    omega
  have hUnion : S_even ∪ S_odd = S := by
    ext a
    dsimp [S_even, S_odd]
    simp only [Finset.mem_union, Finset.mem_filter]
    have hParity : Even ⌊a⌋ ∨ Odd ⌊a⌋ := Int.even_or_odd ⌊a⌋
    tauto
  have hWeightSplit :
      (∑ t ∈ S_even, weight t) + (∑ t ∈ S_odd, weight t) = ∑ t ∈ S, weight t := by
    rw [← Finset.sum_union hDisjoint, hUnion]
  have hHeavy :
      (∑ t ∈ S, weight t) ≤ 2 * (∑ t ∈ S_even, weight t) ∨
        (∑ t ∈ S, weight t) ≤ 2 * (∑ t ∈ S_odd, weight t) := by
    omega

  have hBinWeight : ∀ z : ℤ, ∑ t ∈ S.filter (fun u => ⌊u⌋ = z), weight t ≤ L := by
    intro z
    have hEq : S.filter (fun u => ⌊u⌋ = z) =
        S.filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1) := by
      ext a
      simp only [Finset.mem_filter]
      apply and_congr_right'
      exact Int.floor_eq_iff
    rw [hEq]
    exact hL z

  let representative (A : Finset ℝ) (z : ℤ) : ℝ :=
    if h : (A.filter (fun t => ⌊t⌋ = z)).Nonempty then
      (A.filter (fun t => ⌊t⌋ = z)).max' h
    else
      0
  let chooseBins (A : Finset ℝ) : Finset ℝ :=
    (A.image (fun t => ⌊t⌋)).image (representative A)

  have representative_mem (A : Finset ℝ) (z : ℤ)
      (hz : z ∈ A.image (fun t => ⌊t⌋)) : representative A z ∈ A := by
    dsimp [representative]
    have hNonempty : (A.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      rw [Finset.mem_image] at hz
      rcases hz with ⟨t, ht, rfl⟩
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩⟩
    split
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hNonempty)).1
    · contradiction

  have representative_floor (A : Finset ℝ) (z : ℤ)
      (hz : z ∈ A.image (fun t => ⌊t⌋)) : ⌊representative A z⌋ = z := by
    dsimp [representative]
    have hNonempty : (A.filter (fun t => ⌊t⌋ = z)).Nonempty := by
      rw [Finset.mem_image] at hz
      rcases hz with ⟨t, ht, rfl⟩
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩⟩
    split
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hNonempty)).2
    · contradiction

  have chooseBins_subset (A : Finset ℝ) : chooseBins A ⊆ A := by
    intro x hx
    dsimp [chooseBins] at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact representative_mem A z hz

  have chooseBins_floor (A : Finset ℝ) :
      ∀ x ∈ chooseBins A,
        ⌊x⌋ ∈ A.image (fun t => ⌊t⌋) ∧ x = representative A ⌊x⌋ := by
    intro x hx
    dsimp [chooseBins] at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨z, hz, rfl⟩
    have hzFloor := representative_floor A z hz
    rw [hzFloor]
    exact ⟨hz, rfl⟩

  have chooseBins_card (A : Finset ℝ) :
      (chooseBins A).card = (A.image (fun t => ⌊t⌋)).card := by
    dsimp [chooseBins]
    apply Finset.card_image_of_injOn
    intro z₁ hz₁ z₂ hz₂ hRep
    have h₁ := representative_floor A z₁ hz₁
    have h₂ := representative_floor A z₂ hz₂
    rw [hRep] at h₁
    exact h₁.symm.trans h₂

  have separated_of_parity (A : Finset ℝ)
      (hParity : (∀ x ∈ A, Even ⌊x⌋) ∨ (∀ x ∈ A, Odd ⌊x⌋)) :
      RiemannZeta.GuthMaynard.IsSeparated 1 (chooseBins A) := by
    intro x hx y hy hxy
    have hxData := chooseBins_floor A x hx
    have hyData := chooseBins_floor A y hy
    have hFloorNe : ⌊x⌋ ≠ ⌊y⌋ := by
      intro hEq
      apply hxy
      rw [hxData.2, hyData.2, hEq]
    have hxMem : x ∈ A := chooseBins_subset A hx
    have hyMem : y ∈ A := chooseBins_subset A hy
    have hxBounds : (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 :=
      ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
    have hyBounds : (⌊y⌋ : ℝ) ≤ y ∧ y < (⌊y⌋ : ℝ) + 1 :=
      ⟨Int.floor_le y, Int.lt_floor_add_one y⟩
    dsimp [dist]
    by_cases hxyFloor : ⌊x⌋ ≤ ⌊y⌋
    · have hInt : 2 ≤ ⌊y⌋ - ⌊x⌋ := by
        rcases hParity with hEven | hOdd
        · rcases hEven x hxMem with ⟨kx, hkx⟩
          rcases hEven y hyMem with ⟨ky, hky⟩
          omega
        · rcases hOdd x hxMem with ⟨kx, hkx⟩
          rcases hOdd y hyMem with ⟨ky, hky⟩
          omega
      have hReal : (2 : ℝ) ≤ (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) := by exact_mod_cast hInt
      have hYX : 1 ≤ y - x := by linarith
      rw [abs_sub_comm]
      exact hYX.trans (le_abs_self (y - x))
    · have hInt : 2 ≤ ⌊x⌋ - ⌊y⌋ := by
        rcases hParity with hEven | hOdd
        · rcases hEven x hxMem with ⟨kx, hkx⟩
          rcases hEven y hyMem with ⟨ky, hky⟩
          omega
        · rcases hOdd x hxMem with ⟨kx, hkx⟩
          rcases hOdd y hyMem with ⟨ky, hky⟩
          omega
      have hReal : (2 : ℝ) ≤ (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) := by exact_mod_cast hInt
      have hXY : 1 ≤ x - y := by linarith
      exact hXY.trans (le_abs_self (x - y))

  have weighted_by_bins (A : Finset ℝ) (hAS : A ⊆ S) :
      ∑ t ∈ A, weight t ≤ L * (chooseBins A).card := by
    have hFiber :
        (∑ z ∈ A.image (fun t => ⌊t⌋),
          ∑ t ∈ A.filter (fun u => ⌊u⌋ = z), weight t) = ∑ t ∈ A, weight t := by
      have hAll : A.filter (fun t => ⌊t⌋ ∈ A.image (fun u => ⌊u⌋)) = A := by
        apply Finset.filter_eq_self.mpr
        intro t ht
        exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
      have hFiberwise := Finset.sum_fiberwise_eq_sum_filter
        A (A.image (fun t => ⌊t⌋)) (fun t => ⌊t⌋) weight
      rw [hAll] at hFiberwise
      exact hFiberwise
    rw [← hFiber, chooseBins_card]
    calc
      (∑ z ∈ A.image (fun t => ⌊t⌋),
          ∑ t ∈ A.filter (fun u => ⌊u⌋ = z), weight t)
          ≤ ∑ _z ∈ A.image (fun t => ⌊t⌋), L := by
            apply Finset.sum_le_sum
            intro z hz
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (fun t ht => by
                simp only [Finset.mem_filter] at ht ⊢
                exact ⟨hAS ht.1, ht.2⟩)
              (fun _ _ _ => Nat.zero_le _)) (hBinWeight z)
      _ = L * (A.image (fun t => ⌊t⌋)).card := by
        simp [mul_comm]

  have even_subset : S_even ⊆ S := Finset.filter_subset _ _
  have odd_subset : S_odd ⊆ S := Finset.filter_subset _ _
  have evenParity : ∀ x ∈ S_even, Even ⌊x⌋ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have oddParity : ∀ x ∈ S_odd, Odd ⌊x⌋ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2

  rcases hHeavy with hEven | hOdd
  · refine ⟨chooseBins S_even, chooseBins_subset S_even |>.trans even_subset,
      separated_of_parity S_even (Or.inl evenParity), ?_⟩
    calc
      ∑ t ∈ S, weight t ≤ 2 * (∑ t ∈ S_even, weight t) := hEven
      _ ≤ 2 * (L * (chooseBins S_even).card) :=
        Nat.mul_le_mul_left 2 (weighted_by_bins S_even even_subset)
      _ = 2 * L * (chooseBins S_even).card := by ring
  · refine ⟨chooseBins S_odd, chooseBins_subset S_odd |>.trans odd_subset,
      separated_of_parity S_odd (Or.inr oddParity), ?_⟩
    calc
      ∑ t ∈ S, weight t ≤ 2 * (∑ t ∈ S_odd, weight t) := hOdd
      _ ≤ 2 * (L * (chooseBins S_odd).card) :=
        Nat.mul_le_mul_left 2 (weighted_by_bins S_odd odd_subset)
      _ = 2 * L * (chooseBins S_odd).card := by ring

end RiemannZeta.GuthMaynard


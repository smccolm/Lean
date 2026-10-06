import Dubon2026.CompactJetCover

/-! # Uniform small-value estimates over the genuine compact prime-twist family -/

namespace Dubon2026

open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff

theorem exists_pos_mul_lt_finset {ι : Type*} (s : Finset ι) (A B : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 < B i) :
    ∃ η : ℝ, 0 < η ∧ ∀ i ∈ s, A i * η < B i := by
  classical
  revert hA hB
  induction s using Finset.induction_on with
  | empty => exact fun _ _ => ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    intro hA hB
    obtain ⟨η, hη, hb⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hB j (Finset.mem_insert_of_mem hj))
    obtain ⟨ε, hε, he⟩ := exists_pos_mul_lt (hB i (Finset.mem_insert_self i s)) (A i)
    refine ⟨min η ε, lt_min hη hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (mul_le_mul_of_nonneg_left (min_le_right η ε) (hA j (Finset.mem_insert_self j s))).trans_lt he
    · exact (mul_le_mul_of_nonneg_left (min_le_left η ε)
        (hA j (Finset.mem_insert_of_mem hj))).trans_lt (hb j hj)

theorem volume_vertical_sublevel_le_of_patches {a : ℕ → ℂ} {N : ℕ} {σ : ℝ}
    (s : Finset (VerticalJetPatch N))
    (hcover : (Set.univ ×ˢ Icc (0 : ℝ) 1 : Set (PrimeTorus N × ℝ)) ⊆ ⋃ p ∈ s, p.region)
    (hbound : ∀ p ∈ s, ∀ z ∈ p.phases, ∀ t ∈ Icc p.left p.right,
      p.lower ≤ |realVerticalJet a N σ p.order p.component z t|)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsmall : ∀ p ∈ s, (p.order.factorial : ℝ) * (p.order + 1) * ε < p.lower * δ ^ p.order)
    (z : PrimeTorus N) :
    volume {t ∈ Icc (0 : ℝ) 1 | ‖verticalFamily a N σ z t‖ ≤ ε} ≤
      ENNReal.ofReal ((∑ p ∈ s, 2 * (p.order : ℝ)) * δ) := by
  classical
  let q := s.filter (fun p => z ∈ p.phases)
  let S (p : VerticalJetPatch N) :=
    {t ∈ Icc p.left p.right | |realComponent p.component (verticalFamily a N σ z t)| ≤ ε}
  have hsub : {t ∈ Icc (0 : ℝ) 1 | ‖verticalFamily a N σ z t‖ ≤ ε} ⊆ ⋃ p ∈ q, S p := by
    intro t ht
    have hzt : (z, t) ∈ (Set.univ ×ˢ Icc (0 : ℝ) 1 : Set (PrimeTorus N × ℝ)) :=
      ⟨Set.mem_univ z, ht.1⟩
    obtain ⟨p, hp, hz, hleft, hright⟩ := Set.mem_iUnion₂.mp (hcover hzt)
    exact Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hz⟩,
      ⟨⟨hleft.le, hright.le⟩, (abs_realComponent_le_norm _ _).trans ht.2⟩⟩
  have hvol (p : VerticalJetPatch N) (hp : p ∈ q) : volume (S p) ≤ ENNReal.ofReal (2 * p.order * δ) := by
    obtain ⟨hps, hzp⟩ := Finset.mem_filter.mp hp
    apply volume_sublevel_le_of_derivative p.order
      (fun t => realComponent p.component (verticalFamily a N σ z t))
      (contDiff_real_verticalFamily a N σ p.component z) hδ hε (hsmall p hps)
    intro t ht
    rw [iteratedDeriv_real_verticalFamily]
    exact hbound p hps z hzp t ht
  calc
    _ ≤ volume (⋃ p ∈ q, S p) := measure_mono hsub
    _ ≤ ∑ p ∈ q, volume (S p) := measure_biUnion_finset_le q S
    _ ≤ ∑ p ∈ q, ENNReal.ofReal (2 * p.order * δ) := Finset.sum_le_sum hvol
    _ ≤ ∑ p ∈ s, ENNReal.ofReal (2 * p.order * δ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ = ENNReal.ofReal ((∑ p ∈ s, 2 * (p.order : ℝ)) * δ) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro p hp
      positivity

theorem exists_uniform_vertical_sublevel_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ (K : ℕ) (η C : ℝ), 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ z : PrimeTorus N, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        volume {t ∈ Icc (0 : ℝ) 1 | ‖verticalFamily a N σ z t‖ ≤ η * δ ^ K} ≤
          ENNReal.ofReal (C * δ) := by
  classical
  obtain ⟨s, hcover, hs⟩ := exists_finite_vertical_jet_cover hN ha σ
  let K := max 1 (s.sup VerticalJetPatch.order)
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have horder (p : VerticalJetPatch N) (hp : p ∈ s) : p.order ≤ K :=
    (Finset.le_sup hp).trans (le_max_right _ _)
  obtain ⟨η, hη, he⟩ := exists_pos_mul_lt_finset s
    (fun p => (p.order.factorial : ℝ) * (p.order + 1)) VerticalJetPatch.lower
    (by intros; positivity) (fun p hp => (hs p hp).2.1)
  let C := 1 + ∑ p ∈ s, 2 * (p.order : ℝ)
  have hsum : 0 ≤ ∑ p ∈ s, 2 * (p.order : ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨K, η, C, hK, hη, hC, ?_⟩
  intro z δ hδ hδ1
  have hsmall (p : VerticalJetPatch N) (hp : p ∈ s) :
      (p.order.factorial : ℝ) * (p.order + 1) * (η * δ ^ K) < p.lower * δ ^ p.order := by
    have hpow : δ ^ K ≤ δ ^ p.order := pow_le_pow_of_le_one hδ.le hδ1 (horder p hp)
    calc
      _ = ((p.order.factorial : ℝ) * (p.order + 1) * η) * δ ^ K := by ring
      _ < p.lower * δ ^ K := mul_lt_mul_of_pos_right (he p hp) (pow_pos hδ K)
      _ ≤ p.lower * δ ^ p.order := mul_le_mul_of_nonneg_left hpow (hs p hp).2.1.le
  apply (volume_vertical_sublevel_le_of_patches s hcover
    (fun p hp => (hs p hp).2.2) hδ (mul_nonneg hη.le (pow_nonneg hδ.le K)) hsmall z).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hδ.le

end Dubon2026

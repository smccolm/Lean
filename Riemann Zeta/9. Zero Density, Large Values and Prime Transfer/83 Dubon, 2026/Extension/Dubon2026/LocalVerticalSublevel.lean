import Dubon2026.LocalVerticalJetCover

/-! # Small-value estimates uniform on a neighborhood of each real abscissa -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology ENNReal BigOperators

theorem volume_local_vertical_sublevel_le_of_patches {a : ℕ → ℂ} {N : ℕ} {σ b t : ℝ}
    (s : Finset AbscissaJetPatch)
    (hcover : Icc b t ⊆ ⋃ p ∈ s, Ioo p.left p.right)
    (hbound : ∀ p ∈ s, ∀ y ∈ Icc p.left p.right,
      p.lower ≤ |realVerticalJet a N σ p.order p.component 0 y|)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsmall : ∀ p ∈ s, (p.order.factorial : ℝ) * (p.order + 1) * ε < p.lower * δ ^ p.order) :
    volume {y ∈ Icc b t | ‖dirichletSum a N ((σ : ℂ) + Complex.I * y)‖ ≤ ε} ≤
      ENNReal.ofReal ((∑ p ∈ s, 2 * (p.order : ℝ)) * δ) := by
  classical
  let S (p : AbscissaJetPatch) :=
    {y ∈ Icc p.left p.right | |realComponent p.component (verticalFamily a N σ 0 y)| ≤ ε}
  have hsub : {y ∈ Icc b t | ‖dirichletSum a N ((σ : ℂ) + Complex.I * y)‖ ≤ ε} ⊆
      ⋃ p ∈ s, S p := by
    intro y hy
    obtain ⟨p, hp, hl, hr⟩ := Set.mem_iUnion₂.mp (hcover hy.1)
    refine Set.mem_iUnion₂.mpr ⟨p, hp, ⟨⟨hl.le, hr.le⟩, ?_⟩⟩
    exact (abs_realComponent_le_norm _ _).trans (by simpa only [verticalFamily_zero_phase] using hy.2)
  have hvol (p : AbscissaJetPatch) (hp : p ∈ s) :
      volume (S p) ≤ ENNReal.ofReal (2 * p.order * δ) := by
    apply volume_sublevel_le_of_derivative p.order
      (fun y => realComponent p.component (verticalFamily a N σ 0 y))
      (contDiff_real_verticalFamily a N σ p.component 0) hδ hε (hsmall p hp)
    intro y hy
    rw [iteratedDeriv_real_verticalFamily]
    exact hbound p hp y hy
  calc
    _ ≤ volume (⋃ p ∈ s, S p) := measure_mono hsub
    _ ≤ ∑ p ∈ s, volume (S p) := measure_biUnion_finset_le s S
    _ ≤ ∑ p ∈ s, ENNReal.ofReal (2 * p.order * δ) := Finset.sum_le_sum hvol
    _ = ENNReal.ofReal ((∑ p ∈ s, 2 * (p.order : ℝ)) * δ) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro p hp
      positivity

theorem exists_local_vertical_sublevel_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ b t : ℝ) :
    ∃ (V : Set ℝ) (K : ℕ) (η C : ℝ), V ∈ 𝓝 σ ∧ 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ x ∈ V, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        volume {y ∈ Icc b t | ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖ ≤ η * δ ^ K} ≤
          ENNReal.ofReal (C * δ) := by
  classical
  obtain ⟨s, V, hV, hcover, hs⟩ := exists_finite_local_vertical_jet_cover hN ha σ b t
  let K := max 1 (s.sup AbscissaJetPatch.order)
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have horder (p : AbscissaJetPatch) (hp : p ∈ s) : p.order ≤ K :=
    (Finset.le_sup hp).trans (le_max_right _ _)
  obtain ⟨η, hη, he⟩ := exists_pos_mul_lt_finset s
    (fun p => (p.order.factorial : ℝ) * (p.order + 1)) AbscissaJetPatch.lower
    (by intros; positivity) (fun p hp => (hs p hp).1)
  let C := 1 + ∑ p ∈ s, 2 * (p.order : ℝ)
  have hsum : 0 ≤ ∑ p ∈ s, 2 * (p.order : ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨V, K, η, C, hV, hK, hη, hC, ?_⟩
  intro x hx δ hδ hδ1
  have hsmall (p : AbscissaJetPatch) (hp : p ∈ s) :
      (p.order.factorial : ℝ) * (p.order + 1) * (η * δ ^ K) < p.lower * δ ^ p.order := by
    have hpow : δ ^ K ≤ δ ^ p.order := pow_le_pow_of_le_one hδ.le hδ1 (horder p hp)
    calc
      _ = ((p.order.factorial : ℝ) * (p.order + 1) * η) * δ ^ K := by ring
      _ < p.lower * δ ^ K := mul_lt_mul_of_pos_right (he p hp) (pow_pos hδ K)
      _ ≤ p.lower * δ ^ p.order := mul_le_mul_of_nonneg_left hpow (hs p hp).1.le
  apply (volume_local_vertical_sublevel_le_of_patches s hcover
    (fun p hp => (hs p hp).2 x hx) hδ (mul_nonneg hη.le (pow_nonneg hδ.le K)) hsmall).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hδ.le

end Dubon2026

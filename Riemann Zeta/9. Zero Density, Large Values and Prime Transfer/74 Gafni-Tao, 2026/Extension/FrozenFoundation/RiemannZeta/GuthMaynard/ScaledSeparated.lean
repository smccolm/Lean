import RiemannZeta.GuthMaynard.Separated

open Classical

namespace RiemannZeta.GuthMaynard

/-- The total weight carried by one point after ordinates are divided by `G`. -/
noncomputable def scaledFiberWeight (S : Finset ℝ) (weight : ℝ → ℕ)
    (G u : ℝ) : ℕ :=
  ∑ t ∈ S.filter (fun x => x / G = u), weight t

/--
Weighted separated selection at an arbitrary positive scale.  The local
occupancy assumption is written on normalized ordinates; unlike an informal
change of variables, `scaledFiberWeight` retains the weights of every point
that maps to a normalized ordinate.
-/
theorem scaled_weighted_separated_selection
    (S : Finset ℝ) (weight : ℝ → ℕ) (L : ℕ) {G : ℝ} (hG : 0 < G)
    (hLocal : ∀ z : ℤ,
      ∑ u ∈ (S.image (fun t => t / G)).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1),
        scaledFiberWeight S weight G u ≤ L) :
    ∃ W ⊆ S, IsSeparated G W ∧
      ∑ t ∈ S, weight t ≤ 2 * L * W.card := by
  let A : Finset ℝ := S.image (fun t => t / G)
  let normalizedWeight : ℝ → ℕ := scaledFiberWeight S weight G
  obtain ⟨V, hVA, hVSeparated, hWeight⟩ :=
    weighted_separated_selection A normalizedWeight L (by
      intro z
      simpa [A, normalizedWeight] using hLocal z)
  let W : Finset ℝ := S.filter (fun t => t / G ∈ V)
  have hGne : G ≠ 0 := ne_of_gt hG
  have hScaleInjective : Function.Injective (fun t : ℝ => t / G) := by
    intro x y hxy
    exact (div_left_inj' hGne).mp hxy
  have hImage : W.image (fun t => t / G) = V := by
    ext u
    constructor
    · intro hu
      rw [Finset.mem_image] at hu
      rcases hu with ⟨t, ht, rfl⟩
      exact (Finset.mem_filter.mp ht).2
    · intro hu
      have huA := hVA hu
      change u ∈ S.image (fun t => t / G) at huA
      rw [Finset.mem_image] at huA
      rcases huA with ⟨t, htS, htu⟩
      rw [Finset.mem_image]
      refine ⟨t, Finset.mem_filter.mpr ⟨htS, ?_⟩, htu⟩
      simpa [htu] using hu
  have hWCard : W.card = V.card := by
    have hCard := Finset.card_image_of_injective W hScaleInjective
    rw [hImage] at hCard
    exact hCard.symm
  have hTotalWeight :
      ∑ u ∈ A, normalizedWeight u = ∑ t ∈ S, weight t := by
    have hAll : S.filter (fun t => t / G ∈ A) = S := by
      apply Finset.filter_eq_self.mpr
      intro t ht
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have hFiber := Finset.sum_fiberwise_eq_sum_filter
      S A (fun t : ℝ => t / G) weight
    rw [hAll] at hFiber
    simpa [normalizedWeight, scaledFiberWeight] using hFiber
  refine ⟨W, ?_, ?_, ?_⟩
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro x hx y hy hxy
    have hxV : x / G ∈ V := (Finset.mem_filter.mp hx).2
    have hyV : y / G ∈ V := (Finset.mem_filter.mp hy).2
    have hxyScaled : x / G ≠ y / G := hScaleInjective.ne hxy
    have hSep := hVSeparated (x / G) hxV (y / G) hyV hxyScaled
    rw [Real.dist_eq] at hSep ⊢
    have hDiv : x / G - y / G = (x - y) / G := by field_simp
    rw [hDiv, abs_div, abs_of_pos hG] at hSep
    simpa using (le_div_iff₀ hG).mp hSep
  · rw [hTotalWeight, ← hWCard] at hWeight
    exact hWeight

/-- Radius-`H` windows around `G`-separated ordinates have overlap at most one
when `G > 2H`.  This is the bounded-overlap input used after the logarithmic
Type-II extraction. -/
theorem separated_window_card_le_one (W : Finset ℝ) {G H : ℝ}
    (hSeparated : IsSeparated G W) (hGap : 2 * H < G) (u : ℝ) :
    (W.filter (fun t => dist t u ≤ H)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  simp only [Finset.mem_filter] at hx hy
  by_contra hxy
  have hLower := hSeparated x hx.1 y hy.1 hxy
  have hUpper : dist x y ≤ 2 * H := by
    calc
      dist x y ≤ dist x u + dist u y := dist_triangle x u y
      _ ≤ H + H := add_le_add hx.2 (by simpa [dist_comm] using hy.2)
      _ = 2 * H := by ring
  linarith

end RiemannZeta.GuthMaynard

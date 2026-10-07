import Dubon2026.ZeroFreeBoundaries

/-! # A zero-free inner rectangle retaining every actual interior zero -/

namespace Dubon2026

open Filter Set Complex
open scoped Topology

theorem exists_inner_zero_free_rectangle {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u H : ℝ} (hlu : l < u) (hH : 0 < H) :
    ∃ L U V : ℝ, l < L ∧ L < U ∧ U < u ∧ 0 < V ∧ V < H ∧
      (∀ s ∈ RectangleBorder (⟨L, -V⟩ : ℂ) (⟨U, V⟩ : ℂ), dirichletSum a N s ≠ 0) ∧
      zerosInOpenRectangleFinset a N hN ha L U V =
        zerosInOpenRectangleFinset a N hN ha l u H := by
  classical
  let S := zerosInOpenRectangleFinset a N hN ha l u H
  have he : ∀ᶠ δ : ℝ in 𝓝 0, ∀ s ∈ S,
      l + δ < s.re ∧ s.re < u - δ ∧ |s.im| < H - δ := by
    apply S.eventually_all.mpr
    intro s hs
    obtain ⟨hl, hu, ht, _⟩ := (mem_zerosInOpenRectangleFinset a N hN ha l u H s).mp hs
    have h₁ : ∀ᶠ δ : ℝ in 𝓝 0, l + δ < s.re :=
      (continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const (by simpa using hl)
    have h₂ : ∀ᶠ δ : ℝ in 𝓝 0, s.re < u - δ :=
      continuousAt_const.eventually_lt (continuousAt_const.sub continuousAt_id) (by simpa using hu)
    have h₃ : ∀ᶠ δ : ℝ in 𝓝 0, |s.im| < H - δ :=
      continuousAt_const.eventually_lt (continuousAt_const.sub continuousAt_id) (by simpa using ht)
    exact h₁.and (h₂.and h₃)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, δ < (u - l) / 2 ∧ δ < H :=
    Filter.Eventually.and (Iio_mem_nhds (by linarith : 0 < (u - l) / 2)) (Iio_mem_nhds hH)
  obtain ⟨δ, hδ, hd, hS⟩ := Filter.Eventually.exists (Filter.Eventually.and
    (self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioi 0)
    ((hsmall.and he).filter_mono nhdsWithin_le_nhds))
  obtain ⟨L, hL, hnL⟩ := exists_zero_free_vertical_line hN ha (by linarith : l < l + δ)
  obtain ⟨U, hU, hnU⟩ := exists_zero_free_vertical_line hN ha (by linarith : u - δ < u)
  obtain ⟨V, hV, hnV⟩ := exists_zero_free_symmetric_height hN ha (by linarith : H - δ < H)
  have hVp : 0 < V := by linarith [hd.2, hV.1]
  refine ⟨L, U, V, hL.1, by linarith [hd.1, hL.2, hU.1], hU.2,
    hVp, hV.2, rectangle_boundary_ne_zero_of_lines hVp.le hnL hnU hnV, ?_⟩
  ext s
  constructor
  · intro hs
    rw [mem_zerosInOpenRectangleFinset] at hs ⊢
    exact ⟨hL.1.trans hs.1, hs.2.1.trans hU.2, hs.2.2.1.trans hV.2, hs.2.2.2⟩
  · intro hs
    have hm := hS s hs
    rw [mem_zerosInOpenRectangleFinset] at hs ⊢
    exact ⟨hL.2.trans hm.1, hm.2.1.trans hU.1, hm.2.2.trans hV.1, hs.2.2.2⟩

end Dubon2026

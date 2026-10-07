import Dubon2026.TwistMeanSmallHeight

/-! # The genuine multiplicity count on a horizontal line

At each fixed phase, sufficiently small positive windows retain exactly the zeros
on height zero. Finiteness is inherited from the actual unit rectangle.
-/

namespace Dubon2026

open Filter Set
open scoped Topology BigOperators

noncomputable section

/-- Actual zeros on height zero inside the open real-part interval. -/
def horizontalZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u : ℝ) : Finset ℂ :=
  (zerosInOpenRectangleFinset a N hN ha l u 1).filter (fun s => s.im = 0)

/-- Their actual analytic multiplicity sum. -/
def horizontalZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u : ℝ) : ℕ :=
  ∑ s ∈ horizontalZerosFinset a N hN ha l u, zeroMultiplicity a N s

theorem mem_horizontalZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u : ℝ) (s : ℂ) :
    s ∈ horizontalZerosFinset a N hN ha l u ↔
      l < s.re ∧ s.re < u ∧ s.im = 0 ∧ dirichletSum a N s = 0 := by
  classical
  simp only [horizontalZerosFinset, Finset.mem_filter, mem_zerosInOpenRectangleFinset]
  constructor
  · rintro ⟨⟨hl, hu, _, hz⟩, ht⟩
    exact ⟨hl, hu, ht, hz⟩
  · rintro ⟨hl, hu, ht, hz⟩
    exact ⟨⟨hl, hu, by simp [ht], hz⟩, ht⟩

theorem eventually_small_rectangle_eq_horizontal (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∀ᶠ H : ℝ in 𝓝[>] 0, zerosInOpenRectangleFinset a N hN ha l u H =
      horizontalZerosFinset a N hN ha l u := by
  classical
  let S := zerosInOpenRectangleFinset a N hN ha l u 1
  have he : ∀ᶠ H : ℝ in 𝓝 0, ∀ s ∈ S, s.im ≠ 0 → H < |s.im| := by
    apply S.eventually_all.mpr
    intro s _
    by_cases hs : s.im = 0
    · exact Eventually.of_forall (fun _ h => (h hs).elim)
    · exact Filter.Eventually.mono (Iio_mem_nhds (abs_pos.mpr hs)) (fun _ h _ => h)
  have hsmall : ∀ᶠ H : ℝ in 𝓝[>] 0, H < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, hsmall, self_mem_nhdsWithin] with H hH hH₁ hHp
  ext s
  rw [mem_zerosInOpenRectangleFinset, mem_horizontalZerosFinset]
  constructor
  · rintro ⟨hl, hu, ht, hz⟩
    have hs : s ∈ S := (mem_zerosInOpenRectangleFinset a N hN ha l u 1 s).mpr
      ⟨hl, hu, ht.trans hH₁, hz⟩
    have hi : s.im = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hH s hs hn).le) ht
    exact ⟨hl, hu, hi, hz⟩
  · rintro ⟨hl, hu, ht, hz⟩
    exact ⟨hl, hu, by simpa only [ht, abs_zero] using hHp, hz⟩

theorem eventually_small_count_eq_horizontal (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∀ᶠ H : ℝ in 𝓝[>] 0, verticalZeroCount a N hN ha l u H =
      horizontalZeroCount a N hN ha l u := by
  filter_upwards [eventually_small_rectangle_eq_horizontal a N hN ha l u] with H hH
  simp only [verticalZeroCount, horizontalZeroCount, hH]

theorem horizontalZeroCount_le_vertical (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {H : ℝ} (hH : 0 < H) :
    horizontalZeroCount a N hN ha l u ≤ verticalZeroCount a N hN ha l u H := by
  apply Finset.sum_le_sum_of_subset
  intro s hs
  rw [mem_horizontalZerosFinset] at hs
  rw [mem_zerosInOpenRectangleFinset]
  exact ⟨hs.1, hs.2.1, by simpa only [hs.2.2.1, abs_zero] using hH, hs.2.2.2⟩

end

end Dubon2026

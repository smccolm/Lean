import Dubon2026.ZeroFreeHalfPlanes
import Dubon2026.DirichletZeros

/-! # The literal total and outside-band multiplicity counts -/

namespace Dubon2026

open Set
open scoped BigOperators

noncomputable section

theorem finite_verticalZeros {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (T : ℝ) :
    {s : ℂ | |s.im| < T ∧ dirichletSum a N s = 0}.Finite := by
  obtain ⟨l, u, _, hb⟩ := exists_zero_containing_vertical_strip hN ha
  apply (finite_zerosInOpenRectangle hN ha l u T).subset
  intro s hs
  exact ⟨(hb s hs.2).1, (hb s hs.2).2, hs⟩

/-- All actual zeros with the source's open symmetric height cutoff. -/
def verticalZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0) (T : ℝ) : Finset ℂ :=
  (finite_verticalZeros hN ha T).toFinset

theorem mem_verticalZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (T : ℝ) (s : ℂ) :
    s ∈ verticalZerosFinset a N hN ha T ↔ |s.im| < T ∧ dirichletSum a N s = 0 := by
  simp only [verticalZerosFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The total actual multiplicity count below symmetric height `T`. -/
def totalVerticalZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0) (T : ℝ) : ℕ :=
  ∑ s ∈ verticalZerosFinset a N hN ha T, zeroMultiplicity a N s

/-- The actual count outside the open band of radius `ε`, including its boundary lines. -/
def outsideVerticalZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (α ε T : ℝ) : ℕ :=
  ∑ s ∈ (verticalZerosFinset a N hN ha T).filter (fun s => ε ≤ |s.re - α|), zeroMultiplicity a N s

theorem totalVerticalZeroCount_eq_strip {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ}
    (hb : ∀ s : ℂ, dirichletSum a N s = 0 → l < s.re ∧ s.re < u) (T : ℝ) :
    totalVerticalZeroCount a N hN ha T = verticalZeroCount a N hN ha l u T := by
  have he : verticalZerosFinset a N hN ha T = zerosInOpenRectangleFinset a N hN ha l u T := by
    ext s
    rw [mem_verticalZerosFinset, mem_zerosInOpenRectangleFinset]
    exact ⟨fun h => ⟨(hb s h.2).1, (hb s h.2).2, h⟩, fun h => h.2.2⟩
  simp only [totalVerticalZeroCount, verticalZeroCount, he]

theorem outsideVerticalZeroCount_add_inside {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (α ε T : ℝ) :
    outsideVerticalZeroCount a N hN ha α ε T +
      verticalZeroCount a N hN ha (α - ε) (α + ε) T = totalVerticalZeroCount a N hN ha T := by
  classical
  have he : (verticalZerosFinset a N hN ha T).filter (fun s => ¬ε ≤ |s.re - α|) =
      zerosInOpenRectangleFinset a N hN ha (α - ε) (α + ε) T := by
    ext s
    rw [Finset.mem_filter, mem_verticalZerosFinset, mem_zerosInOpenRectangleFinset]
    simp only [not_le, abs_lt]
    constructor
    · rintro ⟨⟨ht, hz⟩, hl, hu⟩
      exact ⟨by linarith, by linarith, ht, hz⟩
    · rintro ⟨hl, hu, ht, hz⟩
      exact ⟨⟨ht, hz⟩, by linarith, by linarith⟩
  unfold outsideVerticalZeroCount verticalZeroCount totalVerticalZeroCount
  rw [← he]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

end

end Dubon2026

import Dubon2026.DirichletZeros

/-! # Monotonicity of the literal multiplicity count with respect to the open strip -/

namespace Dubon2026

theorem verticalZeroCount_mono_interval {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u L U : ℝ} (hL : L ≤ l) (hU : u ≤ U) (T : ℝ) :
    verticalZeroCount a N hN ha l u T ≤ verticalZeroCount a N hN ha L U T := by
  apply Finset.sum_le_sum_of_subset
  intro s hs
  rw [mem_zerosInOpenRectangleFinset] at hs ⊢
  exact ⟨hL.trans_lt hs.1, hs.2.1.trans_le hU, hs.2.2⟩

theorem verticalZeroCount_empty_interval {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hu : u ≤ l) (T : ℝ) :
    verticalZeroCount a N hN ha l u T = 0 := by
  have he : zerosInOpenRectangleFinset a N hN ha l u T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hh := (mem_zerosInOpenRectangleFinset a N hN ha l u T s).mp hs
    exact (not_lt_of_ge hu) (hh.1.trans hh.2.1)
  simp [verticalZeroCount, he]

end Dubon2026

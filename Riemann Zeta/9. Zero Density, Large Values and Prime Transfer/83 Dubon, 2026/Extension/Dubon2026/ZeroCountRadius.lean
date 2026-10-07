import Dubon2026.TotalVerticalZeros

/-! # Monotonicity of the actual outside-band count in its radius -/

namespace Dubon2026

open Set

theorem outsideVerticalZeroCount_mono_radius {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (α T : ℝ) {η ε : ℝ} (h : η ≤ ε) :
    outsideVerticalZeroCount a N hN ha α ε T ≤ outsideVerticalZeroCount a N hN ha α η T := by
  classical
  unfold outsideVerticalZeroCount
  apply Finset.sum_le_sum_of_subset
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, h.trans hs.2⟩

end Dubon2026

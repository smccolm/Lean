import TaoTrudgianYang2025.SquareProductCount
open TaoTrudgianYang2025.CubicJointCount
open scoped BigOperators
example (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖∑ n∈Finset.Icc 5 5, z n‖ ≤ 1 := by
  simpa using cubic_source_trim z hz 5 5 0 (by norm_num)
example (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖∑ n∈Finset.Icc 5 9, z n‖ ≤ 5 := by
  have h := cubic_source_trim z hz 5 9 2 (by norm_num)
  norm_num at h
  exact h

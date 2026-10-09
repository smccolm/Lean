import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-! # Quadratic characters of the actual real unit group -/

namespace Dubon2026

noncomputable section

/-- Every positive original real unit is the square of an actual real unit. -/
theorem realUnit_positive_square (u : ℝˣ) (hu : 0 < u.val) :
    ∃ v : ℝˣ, v ^ 2 = u := by
  refine ⟨Units.mk0 (Real.sqrt u.val) (ne_of_gt (Real.sqrt_pos.2 hu)), ?_⟩
  apply Units.ext
  exact Real.sq_sqrt (le_of_lt hu)

/-- A quadratic character of the genuine real unit group is trivial on all positive units, without a continuity assumption. -/
theorem realQuadraticCharacter_positive (ψ : ℝˣ →* ℂ) (hψ : ∀ u, ψ u ^ 2 = 1)
    (u : ℝˣ) (hu : 0 < u.val) : ψ u = 1 := by
  obtain ⟨v, hv⟩ := realUnit_positive_square u hu
  rw [← hv, map_pow, hψ]

/-- On negative original real units the same quadratic character has precisely its value at minus one. -/
theorem realQuadraticCharacter_negative (ψ : ℝˣ →* ℂ) (hψ : ∀ u, ψ u ^ 2 = 1)
    (u : ℝˣ) (hu : u.val < 0) : ψ u = ψ (-1) := by
  have hn : 0 < (-u).val := neg_pos.mpr hu
  have he : u = (-1 : ℝˣ) * (-u) := by simp
  rw [he, map_mul, realQuadraticCharacter_positive ψ hψ (-u) hn, mul_one]

end
end Dubon2026

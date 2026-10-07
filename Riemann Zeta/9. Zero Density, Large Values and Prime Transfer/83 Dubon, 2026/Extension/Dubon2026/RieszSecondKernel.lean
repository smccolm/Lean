import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The exact positive quadratic kernel for second Riesz smoothing -/

namespace Dubon2026

noncomputable section

/-- The genuine second Riesz kernel, including its zero extension below the cutoff. -/
def rieszSecondKernel (u : ℝ) : ℝ := max u 0 ^ 2 / 2

/-- The unnormalized second forward difference of an actual real function. -/
def rieszSecondDifference (F : ℝ → ℝ) (x h : ℝ) : ℝ :=
  F (x + 2 * h) - 2 * F (x + h) + F x

/-- The Riesz kernel is nonnegative everywhere. -/
theorem rieszSecondKernel_nonneg (u : ℝ) : 0 ≤ rieszSecondKernel u := by
  unfold rieszSecondKernel
  positivity

/-- Below the cutoff the genuine Riesz kernel vanishes. -/
theorem rieszSecondKernel_eq_zero {u : ℝ} (hu : u ≤ 0) : rieszSecondKernel u = 0 := by
  simp [rieszSecondKernel, max_eq_right hu]

/-- Above the cutoff the kernel is exactly the factorial-normalized quadratic weight. -/
theorem rieszSecondKernel_eq {u : ℝ} (hu : 0 ≤ u) : rieszSecondKernel u = u ^ 2 / 2 := by
  rw [rieszSecondKernel, max_eq_left hu]

/-- The second difference equals h² wherever the full smoothing interval lies above the cutoff. -/
theorem rieszSecondKernel_difference_eq {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    rieszSecondDifference rieszSecondKernel u h = h ^ 2 := by
  rw [rieszSecondDifference, rieszSecondKernel_eq (by linarith),
    rieszSecondKernel_eq (by linarith), rieszSecondKernel_eq hu]
  ring

/-- Across the cutoff the actual second difference stays between zero and h². -/
theorem rieszSecondKernel_difference_bounds {u h : ℝ} (hh : 0 ≤ h) :
    0 ≤ rieszSecondDifference rieszSecondKernel u h ∧
      rieszSecondDifference rieszSecondKernel u h ≤ h ^ 2 := by
  by_cases hu : 0 ≤ u
  · rw [rieszSecondKernel_difference_eq hu hh]
    exact ⟨sq_nonneg h, le_rfl⟩
  have hu0 : u ≤ 0 := le_of_not_ge hu
  by_cases hu1 : 0 ≤ u + h
  · rw [rieszSecondDifference, rieszSecondKernel_eq (by linarith),
      rieszSecondKernel_eq hu1, rieszSecondKernel_eq_zero hu0]
    constructor
    · nlinarith [sq_nonneg h, mul_nonneg hu1 (show 0 ≤ h - u by linarith)]
    · nlinarith [sq_nonneg u]
  have hu1' : u + h ≤ 0 := le_of_not_ge hu1
  by_cases hu2 : 0 ≤ u + 2 * h
  · rw [rieszSecondDifference, rieszSecondKernel_eq hu2,
      rieszSecondKernel_eq_zero hu1', rieszSecondKernel_eq_zero hu0]
    constructor
    · nlinarith [sq_nonneg (u + 2 * h)]
    · nlinarith [sq_nonneg h,
        mul_nonneg (show 0 ≤ h - (u + 2 * h) by linarith) (show 0 ≤ h + (u + 2 * h) by linarith)]
  · rw [rieszSecondDifference, rieszSecondKernel_eq_zero (le_of_not_ge hu2),
      rieszSecondKernel_eq_zero hu1', rieszSecondKernel_eq_zero hu0]
    constructor <;> nlinarith [sq_nonneg h]

/-- The second difference is linear on sums of actual functions. -/
theorem rieszSecondDifference_add (F G : ℝ → ℝ) (x h : ℝ) :
    rieszSecondDifference (fun t => F t + G t) x h =
      rieszSecondDifference F x h + rieszSecondDifference G x h := by
  simp only [rieszSecondDifference]
  ring

/-- The exact cubic main term has the expected linear second difference. -/
theorem rieszSecondDifference_cubic (c x h : ℝ) :
    rieszSecondDifference (fun t => c * t ^ 3 / 6) x h = c * h ^ 2 * (x + h) := by
  simp only [rieszSecondDifference]
  ring

end
end Dubon2026

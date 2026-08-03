import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

open Complex

noncomputable section

namespace RiemannZeta

/-- Horizontal/vertical parametrization of points s(σ, t) = σ + i * t for σ, t ∈ ℝ. -/
def point (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * I

@[simp]
lemma point_re (σ t : ℝ) : (point σ t).re = σ := by
  simp [point]

@[simp]
lemma point_im (σ t : ℝ) : (point σ t).im = t := by
  simp [point]

/-- Reflection identity across the critical point s = 1/2: 1 - s(σ, t) = s(1 - σ, -t). -/
theorem one_sub_point (σ t : ℝ) :
    1 - point σ t = point (1 - σ) (-t) := by
  apply Complex.ext <;> simp [point]

/-- Complex conjugation of a point: star (s(σ, t)) = s(σ, -t). -/
theorem star_point (σ t : ℝ) :
    star (point σ t) = point σ (-t) := by
  apply Complex.ext <;> simp [point]

/-- Functional equation reflection for completed Riemann Zeta: Λ(σ + i t) = Λ(1 - σ - i t). -/
theorem completedRiemannZeta_reflection (σ t : ℝ) :
    completedRiemannZeta (point σ t) =
      completedRiemannZeta (point (1 - σ) (-t)) := by
  have h := (completedRiemannZeta_one_sub (point σ t)).symm
  rw [one_sub_point] at h
  exact h

/-- Dual zero equivalence across functional reflection: Λ(σ + i t) = 0 ↔ Λ(1 - σ - i t) = 0. -/
theorem completedRiemannZeta_zero_reflection_iff (σ t : ℝ) :
    completedRiemannZeta (point σ t) = 0 ↔
      completedRiemannZeta (point (1 - σ) (-t)) = 0 := by
  rw [completedRiemannZeta_reflection]

/-- Norm reflection invariance: ‖Λ(σ + i t)‖ = ‖Λ(1 - σ - i t)‖. -/
theorem completedRiemannZeta_norm_reflection (σ t : ℝ) :
    ‖completedRiemannZeta (point σ t)‖ =
      ‖completedRiemannZeta (point (1 - σ) (-t))‖ := by
  rw [completedRiemannZeta_reflection]

/-- Full Fourfold Zero Orbit Theorem:
    If completed Riemann Zeta vanishes at σ + i t, then it vanishes unconditionally at all four symmetry points:
    1. σ + i t
    2. (1 - σ) - i t
    3. σ - i t
    4. (1 - σ) + i t -/
theorem completedRiemannZeta_fourfold_zero_orbit (σ t : ℝ)
    (h_zero : completedRiemannZeta (point σ t) = 0) :
    completedRiemannZeta (point σ t) = 0 ∧
    completedRiemannZeta (point (1 - σ) (-t)) = 0 ∧
    completedRiemannZeta (point σ (-t)) = 0 ∧
    completedRiemannZeta (point (1 - σ) t) = 0 := by
  refine ⟨h_zero, ?_, ?_, ?_⟩
  · rwa [← completedRiemannZeta_zero_reflection_iff]
  · have h_conj : completedRiemannZeta (point σ (-t)) = star (completedRiemannZeta (point σ t)) := by
      rw [← star_point]
      exact (completedRiemannZeta_conj (point σ t)).symm
    rw [h_conj, h_zero, star_zero]
  · have h_conj_refl : completedRiemannZeta (point (1 - σ) t) =
        completedRiemannZeta (point (1 - (1 - σ)) (-t)) := by
      exact completedRiemannZeta_reflection (1 - σ) t
    rw [sub_sub_cancel] at h_conj_refl
    rw [h_conj_refl]
    have h_conj : completedRiemannZeta (point σ (-t)) = star (completedRiemannZeta (point σ t)) := by
      rw [← star_point]
      exact (completedRiemannZeta_conj (point σ t)).symm
    rw [h_conj, h_zero, star_zero]

end RiemannZeta

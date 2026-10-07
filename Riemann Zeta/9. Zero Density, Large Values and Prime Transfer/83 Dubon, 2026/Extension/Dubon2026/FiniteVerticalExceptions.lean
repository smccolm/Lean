import Dubon2026.RectangleRealParts

/-! # Finitely many exceptional abscissae in a fixed compact zero-counting rectangle -/

namespace Dubon2026

open Complex Set

theorem exists_finite_vertical_segment_exceptions {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T : ℝ) :
    ∃ Z : Finset ℝ, ∀ x ∈ Icc l u, x ∉ Z →
      ∀ y ∈ Icc (-T) T, dirichletSum a N ((x : ℂ) + I * y) ≠ 0 := by
  classical
  have hfin := finite_dirichletZeros_in_compact hN ha (isCompact_closedBall (0 : ℂ) (|l| + |u| + |T|))
  refine ⟨hfin.toFinset.image Complex.re, ?_⟩
  intro x hx hxZ y hy hz
  apply hxZ
  apply Finset.mem_image.mpr
  refine ⟨(x : ℂ) + I * y, ?_, by simp⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hxabs : |x| ≤ |l| + |u| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le l, abs_nonneg u, hx.1]
    · linarith [le_abs_self u, abs_nonneg l, hx.2]
  have hyabs : |y| ≤ |T| := (abs_le.mpr hy).trans (le_abs_self T)
  exact ((x : ℂ) + I * y).norm_le_abs_re_add_abs_im.trans (by simpa using add_le_add hxabs hyabs)

theorem rectangle_boundary_ne_zero_of_segments {a : ℕ → ℂ} {N : ℕ} {l u T : ℝ}
    (hT : 0 ≤ T)
    (hl : ∀ y ∈ Icc (-T) T, dirichletSum a N ((l : ℂ) + I * y) ≠ 0)
    (hu : ∀ y ∈ Icc (-T) T, dirichletSum a N ((u : ℂ) + I * y) ≠ 0)
    (ht : ∀ s : ℂ, |s.im| = T → dirichletSum a N s ≠ 0) :
    ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0 := by
  intro s hs
  rcases hs with ((hs | hs) | hs) | hs
  · apply ht s
    have he : s.im = -T := hs.2
    rw [he, abs_neg, abs_of_nonneg hT]
  · have hy : s.im ∈ Icc (-T) T := by simpa only [uIcc_of_le (neg_le_self hT)] using hs.2
    have he : s = (l : ℂ) + I * s.im := by
      apply Complex.ext
      · simpa using hs.1
      · simp
    rw [he]
    exact hl s.im hy
  · apply ht s
    have he : s.im = T := hs.2
    rw [he, abs_of_nonneg hT]
  · have hy : s.im ∈ Icc (-T) T := by simpa only [uIcc_of_le (neg_le_self hT)] using hs.2
    have he : s = (u : ℂ) + I * s.im := by
      apply Complex.ext
      · simpa using hs.1
      · simp
    rw [he]
    exact hu s.im hy

end Dubon2026

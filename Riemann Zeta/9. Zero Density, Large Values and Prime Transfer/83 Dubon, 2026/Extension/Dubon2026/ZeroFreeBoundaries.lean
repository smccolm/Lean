import Dubon2026.RectangleZeroCount
import Dubon2026.LogTruncation
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Genuine nonvanishing rectangle boundaries chosen from the actual zero set -/

namespace Dubon2026

open Set Complex

theorem exists_zero_free_vertical_line {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l < u) :
    ∃ σ ∈ Ioo l u, ∀ s : ℂ, s.re = σ → dirichletSum a N s ≠ 0 := by
  have hd := ((countable_dirichletZeros hN ha).image Complex.re).dense_compl ℝ
  obtain ⟨σ, hi, hσ⟩ := hd.inter_open_nonempty (Ioo l u) isOpen_Ioo (nonempty_Ioo.mpr hlu)
  refine ⟨σ, hi, ?_⟩
  intro s hs hz
  exact hσ ⟨s, hz, hs⟩

theorem exists_zero_free_symmetric_height {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l < u) :
    ∃ T ∈ Ioo l u, ∀ s : ℂ, |s.im| = T → dirichletSum a N s ≠ 0 := by
  have hd := ((countable_dirichletZeros hN ha).image (fun s : ℂ => |s.im|)).dense_compl ℝ
  obtain ⟨T, hi, hT⟩ := hd.inter_open_nonempty (Ioo l u) isOpen_Ioo (nonempty_Ioo.mpr hlu)
  refine ⟨T, hi, ?_⟩
  intro s hs hz
  exact hT ⟨s, hz, hs⟩

theorem rectangle_boundary_ne_zero_of_lines {a : ℕ → ℂ} {N : ℕ} {l u T : ℝ}
    (hT : 0 ≤ T)
    (hl : ∀ s : ℂ, s.re = l → dirichletSum a N s ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → dirichletSum a N s ≠ 0)
    (ht : ∀ s : ℂ, |s.im| = T → dirichletSum a N s ≠ 0) :
    ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0 := by
  intro s hs
  rcases hs with ((hs | hs) | hs) | hs
  · apply ht s
    have he : s.im = -T := hs.2
    rw [he, abs_neg, abs_of_nonneg hT]
  · exact hl s hs.1
  · apply ht s
    have he : s.im = T := hs.2
    rw [he, abs_of_nonneg hT]
  · exact hu s hs.1

theorem exists_arbitrarily_high_count_contour {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ s : ℂ, s.re = l → dirichletSum a N s ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → dirichletSum a N s ≠ 0) (H : ℝ) :
    ∃ T : ℝ, max H 0 < T ∧ T < max H 0 + 1 ∧
      RectangleIntegral' (logDeriv (dirichletSum a N)) (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
        (verticalZeroCount a N hN ha l u T : ℂ) := by
  obtain ⟨T, hT, ht⟩ := exists_zero_free_symmetric_height hN ha
    (show max H 0 < max H 0 + 1 by linarith)
  have hpos : 0 ≤ T := (le_max_right H 0).trans hT.1.le
  exact ⟨T, hT.1, hT.2, rectangleIntegral_logDeriv_eq_verticalZeroCount hN ha hlu hpos
    (rectangle_boundary_ne_zero_of_lines hpos hl hu ht)⟩

end Dubon2026

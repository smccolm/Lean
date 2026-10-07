import Dubon2026.RegularAbscissae

/-! # Regular abscissae approximate a point of continuous Jessen derivative from either side -/

namespace Dubon2026

open Set Filter
open scoped Topology

theorem exists_regular_abscissa_left_close {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ)
    (hc : ContinuousAt (fun y => derivWithin (jessenFunction a N) (Ioi y) y) x)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ y ∈ Ioo (x - r) x,
      |derivWithin (jessenFunction a N) (Ioi y) y -
        derivWithin (jessenFunction a N) (Ioi x) x| < ε ∧
      (∀ s : ℂ, s.re = y → dirichletSum a N s ≠ 0) ∧
      HasDerivAt (jessenFunction a N) (derivWithin (jessenFunction a N) (Ioi y) y) y := by
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc ε hε
  have hp : 0 < min r δ := lt_min hr hδ
  obtain ⟨y, hy, hn, hd, _⟩ := exists_regular_abscissa hN ha
    (show x - min r δ < x by linarith)
  refine ⟨y, ⟨?_, hy.2⟩, ?_, hn, hd⟩
  · linarith [min_le_left r δ, hy.1]
  · apply (show dist (derivWithin (jessenFunction a N) (Ioi y) y)
      (derivWithin (jessenFunction a N) (Ioi x) x) < ε from hb (by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hy.2)]
        linarith [min_le_right r δ, hy.1]))

theorem exists_regular_abscissa_right_close {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : ℝ)
    (hc : ContinuousAt (fun y => derivWithin (jessenFunction a N) (Ioi y) y) x)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ y ∈ Ioo x (x + r),
      |derivWithin (jessenFunction a N) (Ioi y) y -
        derivWithin (jessenFunction a N) (Ioi x) x| < ε ∧
      (∀ s : ℂ, s.re = y → dirichletSum a N s ≠ 0) ∧
      HasDerivAt (jessenFunction a N) (derivWithin (jessenFunction a N) (Ioi y) y) y := by
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc ε hε
  have hp : 0 < min r δ := lt_min hr hδ
  obtain ⟨y, hy, hn, hd, _⟩ := exists_regular_abscissa hN ha
    (show x < x + min r δ by linarith)
  refine ⟨y, ⟨hy.1, ?_⟩, ?_, hn, hd⟩
  · linarith [min_le_left r δ, hy.2]
  · apply (show dist (derivWithin (jessenFunction a N) (Ioi y) y)
      (derivWithin (jessenFunction a N) (Ioi x) x) < ε from hb (by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hy.1)]
        linarith [min_le_right r δ, hy.2]))

end Dubon2026

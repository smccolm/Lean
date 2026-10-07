import Dubon2026.ConvexDerivatives
import Dubon2026.ZeroFreeBoundaries
import Dubon2026.JessenConvexity
import Mathlib.Topology.Order.Monotone

/-! # Dense differentiable abscissae with genuinely zero-free vertical lines -/

namespace Dubon2026

open Set Filter Function
open scoped Topology

theorem hasDerivAt_convex_of_continuous_rightDeriv {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {x : ℝ}
    (hc : ContinuousAt (fun y => derivWithin f (Ioi y) y) x) :
    HasDerivAt f (derivWithin f (Ioi x) x) x := by
  have he : derivWithin f (Iio x) x = derivWithin f (Ioi x) x := by
    rw [← leftLim_convex_rightDeriv hf]
    exact hc.continuousWithinAt.leftLim_eq
  have hl := hf.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp : x ∈ interior univ)
  have hr := hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp : x ∈ interior univ)
  rw [he] at hl
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl,
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr⟩

theorem continuousAt_convex_rightDeriv_of_hasDerivAt {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {x d : ℝ} (hd : HasDerivAt f d x) :
    ContinuousAt (fun y => derivWithin f (Ioi y) y) x := by
  apply (monotone_convex_rightDeriv hf).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [leftLim_convex_rightDeriv hf, rightLim_convex_rightDeriv hf,
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x),
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)]

theorem exists_regular_abscissa {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l < u) :
    ∃ x ∈ Ioo l u, (∀ s : ℂ, s.re = x → dirichletSum a N s ≠ 0) ∧
      HasDerivAt (jessenFunction a N)
        (derivWithin (jessenFunction a N) (Ioi x) x) x ∧
      ContinuousAt (fun y => derivWithin (jessenFunction a N) (Ioi y) y) x := by
  have hf := convexOn_jessenFunction hN ha
  have hcount := ((countable_dirichletZeros hN ha).image Complex.re).union
    (monotone_convex_rightDeriv hf).countable_not_continuousAt
  obtain ⟨x, hx, hgood⟩ := hcount.dense_compl ℝ |>.inter_open_nonempty
    (Ioo l u) isOpen_Ioo (nonempty_Ioo.mpr hlu)
  have hc : ContinuousAt (fun y => derivWithin (jessenFunction a N) (Ioi y) y) x := by
    by_contra h
    exact hgood (Or.inr h)
  refine ⟨x, hx, ?_, hasDerivAt_convex_of_continuous_rightDeriv hf hc, hc⟩
  intro s hs hz
  exact hgood (Or.inl ⟨s, hz, hs⟩)

end Dubon2026

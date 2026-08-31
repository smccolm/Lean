import GafniTao.FordZeroDetectorEdges
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Convexity input for Ford's explicit real-axis zeta bound

Ford bounds the zeta series by integrating the convex function
`x ↦ x⁻ˢ` over unit intervals centred at the integers.  This file proves
the source convexity statement on the entire physical range `x ≥ 1`.
-/

open Set

namespace GafniTao

theorem ford_convexOn_rpow_neg {sigma : ℝ} (hsigma : 0 < sigma) :
    ConvexOn ℝ (Ici 1) (fun x : ℝ => x ^ (-sigma)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    have hx1 : 1 ≤ x := hx
    exact (Real.continuousAt_rpow_const x (-sigma)
      (Or.inl (by linarith : x ≠ 0))).continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    exact (Real.hasDerivAt_rpow_const (x := x) (p := -sigma)
      (Or.inl hxpos.ne')).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    exact ((Real.hasDerivAt_rpow_const (x := x) (p := -sigma - 1)
      (Or.inl hxpos.ne')).const_mul (-sigma)).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    have hpow : 0 < x ^ (-sigma - 2) := Real.rpow_pos_of_pos hxpos _
    have hcoeff : 0 < (-sigma) * (-sigma - 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    rw [show -sigma - 1 - 1 = -sigma - 2 by ring]
    rw [← mul_assoc]
    exact mul_nonneg hcoeff.le hpow.le

end GafniTao

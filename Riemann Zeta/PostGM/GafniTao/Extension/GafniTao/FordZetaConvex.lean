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
  · fun_prop
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      linarith
    exact (Real.hasDerivAt_rpow_const (Or.inl hxpos.ne') (-sigma)).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      linarith
    exact ((Real.hasDerivAt_rpow_const (Or.inl hxpos.ne') (-sigma - 1)).const_mul
      (-sigma)).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      linarith
    have hpow : 0 < x ^ (-sigma - 2) := Real.rpow_pos_of_pos hxpos _
    positivity

end GafniTao

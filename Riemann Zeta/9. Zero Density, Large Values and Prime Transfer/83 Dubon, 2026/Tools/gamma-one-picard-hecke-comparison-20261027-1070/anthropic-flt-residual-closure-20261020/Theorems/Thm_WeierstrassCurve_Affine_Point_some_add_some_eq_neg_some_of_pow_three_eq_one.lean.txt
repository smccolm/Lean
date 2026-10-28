import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one

theorem WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one
    {k : Type*} [Field k] [DecidableEq k] (B w : k) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) {x y : k}
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
    (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
    (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y) (hx : x ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.solution

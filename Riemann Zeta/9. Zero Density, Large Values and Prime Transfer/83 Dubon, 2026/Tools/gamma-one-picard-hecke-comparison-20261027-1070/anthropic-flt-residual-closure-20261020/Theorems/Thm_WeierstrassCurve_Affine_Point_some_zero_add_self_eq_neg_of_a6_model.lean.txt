import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model

theorem WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.solution
